import Plausible.GeneratingGoodGenerators.UnificationMonad

open Lean

----------------------------------------------
-- Type definitions
----------------------------------------------

/-- A `HypothesisExpr` is a datatype representing a hypothesis for a
    constructor of an inductive relation, consisting of a constructor name
    applied to some list of arguments, each of which are `ConstructorExpr`s -/
abbrev HypothesisExpr := Name × List ConstructorExpr

/-- `ToExpr` instance for `HypothesisExpr`
    (for converting `HypothesisExpr`s to Lean `Expr`s) -/
instance : ToExpr HypothesisExpr where
  toExpr (hypExpr : HypothesisExpr) : Expr :=
    let (ctorName, ctorArgs) := hypExpr
    mkAppN (mkConst ctorName) (toExpr <$> ctorArgs.toArray)
  toTypeExpr := mkConst ``Expr

/-- A source is the thing we wish to check/generate/enumerate -/
inductive Source
  | NonRec : HypothesisExpr → Source
  | Rec : Name → List ConstructorExpr → Source
  deriving Repr, BEq, Ord

/-- Producers are either enumerators or generators -/
inductive ProducerSort
  | Enumerator
  | Generator
  deriving Repr, BEq, Ord

/-- The sort of function we are deriving based on an inductive relation:
    determines whether we are deriving a (constrained) generator, enumerator or a checker.

    Note: the `Theorem` constructor is used in the artifact of "Testing Theorems, Fully Automatically"
    for automatically testing whether a theorem holds (we replicate it here for completeness). -/
inductive DeriveSort
  | Generator
  | Enumerator
  | Checker
  | Theorem
  deriving Repr, BEq, Ord

/-- The type of schedule we wish to derive -/
inductive ScheduleSort
  /-- tuple of produced outputs from conclusion of constructor -/
  | ProducerSchedule (producerSort : ProducerSort) (conclusion : List ConstructorExpr)

  /-- checkers need not bother with conclusion of constructor,
      only hypotheses need be checked and conclusion of constructor follows-/
  | CheckerSchedule

  /-- In a `TheoremSchedule`, we check the `conclusion` of the theorem, and take in a `Bool`
      which is true if we need to find a checker by identifying the `DecOpt` instance,
      and false otherwise (we're currently dealing with a function that returns `Option Bool`) -/
  | TheoremSchedule (conclusion : HypothesisExpr) (typeClassUsed : Bool)

  deriving Repr, Ord, BEq


/-- A single step in a generator schedule -/
inductive ScheduleStep
  /-- Unconstrained generation -/
  | Unconstrained : Name → Source → ProducerSort → ScheduleStep

  /-- Generate a value such that a predicate is satisfied -/
  | SuchThat : List (Name × ConstructorExpr) → Source → ProducerSort → ScheduleStep

  /-- Check whether some proposition holds
     (the bool is the desired truth value of the proposition we're checking) -/
  | Check : Source → Bool → ScheduleStep

  /-- Used when you decompose a constructor constrained arg into a
    fresh variable followed by a pattern match -/
  | Match : Name → Pattern → ScheduleStep

  deriving Repr, BEq, Ord

/-- A schedule is a pair consisting of an ordered list of `ScheduleStep`s,
    and the sort of schedule we're dealing with (the latter is the "conclusion" of the schedule) -/
abbrev Schedule := List ScheduleStep × ScheduleSort


/-- Each `ScheduleStep` is associated with a `Density`, which represents a failure mode of a generator -/
inductive Density
  /-- Invokes a call to a checker -/
  | Checking

  /-- A call to `ArbitrarySuchThat`, followed by a pattern-match on the generated value
      (this happens when we want the output of the generator to have a certain shape) -/
  | Backtracking

  /-- a call to `ArbitrarySuchThat` ??? -/
  | Partial

  /-- Unconstrained generation, i.e. calls to `arbitrary` -/
  | Total
  deriving Repr, BEq

/-- Converts a `HypothesisExpr` to a `TSyntax term` -/
def hypothesisExprToTSyntaxTerm (hypExpr : HypothesisExpr) : MetaM (TSyntax `term) := do
  let (ctorName, ctorArgs) := hypExpr
  let ctorArgTerms ← ctorArgs.toArray.mapM constructorExprToTSyntaxTerm
  `($(mkIdent ctorName) $ctorArgTerms:term*)

/-- Converts an `Expr` to a `ConstructorExpr` -/
partial def exprToConstructorExpr (e : Expr) : MetaM ConstructorExpr := do
  match e with
  | .fvar id =>
    let localDecl ← FVarId.getDecl id
    return ConstructorExpr.Unknown localDecl.userName
  | .const name _ =>
    -- Check if this is a constructor
    let env ← getEnv
    if env.isConstructor name then
      return ConstructorExpr.Ctor name []
    else
      return ConstructorExpr.Unknown name
  | .app f arg => do
    let fExpr ← exprToConstructorExpr f
    let argExpr ← exprToConstructorExpr arg
    match fExpr with
    | ConstructorExpr.Ctor name args =>
      return ConstructorExpr.Ctor name (args ++ [argExpr])
    | ConstructorExpr.Unknown name =>
      -- Treat as constructor application if we encounter an application
      return ConstructorExpr.Ctor name [argExpr]
  | _ =>
    -- For other expression types (literals, lambdas, etc.), generate a placeholder name
    return ConstructorExpr.Unknown `unknown

/-- Converts an `Expr` to an `Option HypothesisExpr` -/
def exprToHypothesisExpr (e : Expr) : MetaM (Option HypothesisExpr) := do
  let (ctorName, args) := e.getAppFnArgs

  let env ← getEnv

  -- Only proceed if `ctorName` refers to a constructor or the name of an `inductive`
  if env.isConstructor ctorName || (← isInductive ctorName) then
    let constructorArgs ← args.mapM exprToConstructorExpr
    return some (ctorName, constructorArgs.toList)
  else
    return none

/-- Updates a `Source` with the result of unification as contained in the `UnknownMap` -/
def updateSource (k : UnknownMap) (src : Source) : UnifyM Source := do
  logWarning m!"updating source {repr src}"
  match src with
  | .NonRec hyp => do
    let hypExpr := toExpr hyp
    logWarning m!"hypExpr is {hypExpr}"

    -- To do so, we first extract the constructor in the hypothesis
    -- and see if it corresponds to a type constructor for a parameterized type `inductive` type (e.g. `List`)
    -- If yes, we can just return the source as is, since the source is just the name of a type
    let (typeConstructor, _) := hypExpr.getAppFnArgs

    try (do
      -- TODO: figure out why this causes tests to fail!
      let inductiveVal ← getConstInfoInduct typeConstructor
      logWarning m!"inductiveVal.all = {inductiveVal.all}"
      logWarning m!"inductiveVal.ctors = {inductiveVal.ctors}"
      logWarning m!"inductiveVal.numParams = {inductiveVal.numParams}"
      pure src)
    catch _ =>
      let (ctorName, args) := hyp
      let updatedArgs ← List.mapM (UnifyM.updateConstructorArg k) args
      return .NonRec (ctorName, updatedArgs)
  | .Rec r tys => do
    let updatedTys ← List.mapM (UnifyM.updateConstructorArg k) tys
    return .Rec r updatedTys

/-- Updates a list of `ScheduleSteps` with the result of unification -/
def updateScheduleSteps (scheduleSteps : List ScheduleStep) : UnifyM (List ScheduleStep) := do
  logWarning "updating scheduleSteps..."
  UnifyM.withConstraints $ fun k => scheduleSteps.mapM (fun step =>
    match step with
    | .Match u p => do
      let updatedScrutinee ← UnifyM.findCanonicalUnknown k u
      let updatedPattern ← UnifyM.updatePattern k p
      return .Match updatedScrutinee updatedPattern
    | .Unconstrained u src producerSort => do
      logWarning m!"in unconstrained case, finding canonical unknown for unknown {u}"
      let updatedUnknown ← UnifyM.findCanonicalUnknown k u
      logWarning m!"updatedUnknown = {updatedUnknown}"
      let updatedSrc ← updateSource k src
      return .Unconstrained updatedUnknown updatedSrc producerSort
    | .SuchThat unknownsAndTypes src dst => do
      let updatedUnknownsAndTypes ← unknownsAndTypes.mapM (fun (u, ty) => do
        let u' ← UnifyM.findCanonicalUnknown k u
        return (u', ty))
      let updatedSource ← updateSource k src
      return .SuchThat updatedUnknownsAndTypes updatedSource dst
    | .Check src polarity => do
      let updatedSrc ← updateSource k src
      return .Check updatedSrc polarity)

/-- Takes the `patterns` and `equalities` fields from `UnifyState` (which are created after
    the conclusion of a constructor has been unified with the top-level arguments to the inductive relation),
    converts them to the appropriate `ScheduleStep`s, and prepends them to the `currentSchedule`.

    - The intuition for prepending these newly-created steps to the existing schedule is that we want to
      make sure all the equalities & pattern-matches needed for the conclusion hold before
      processing the rest of the schedule. -/
def addConclusionPatternsAndEqualitiesToSchedule (patterns : List (Unknown × Pattern)) (equalities : Std.HashSet (Unknown × Unknown)) (currentSchedule : Schedule) : Schedule :=
  let (existingScheduleSteps, scheduleSort) := currentSchedule
  let matchSteps := (Function.uncurry ScheduleStep.Match) <$> patterns
  let equalityCheckSteps := (fun (u1, u2) => ScheduleStep.Check (Source.NonRec (`BEq.beq, [.Unknown u1, .Unknown u2])) true) <$> equalities.toList
  (matchSteps ++ equalityCheckSteps ++ existingScheduleSteps, scheduleSort)
