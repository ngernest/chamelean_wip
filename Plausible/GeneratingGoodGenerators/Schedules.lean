import Lean
import Plausible.GeneratingGoodGenerators.UnificationMonad

open Lean

----------------------------------------------
-- Type definitions
----------------------------------------------

/-- A `HypothesisExpr` is a datatype representing a hypothesis for a
    constructor of an inductive relation, consisting of a constructor name
    applied to some list of arguments, each of which are `ConstructorExpr`s -/
abbrev HypothesisExpr := Name × List ConstructorExpr

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
  | ProducerSchedule (isConstrained : Bool) (producerSort : ProducerSort) (conclusion : Name × ConstructorExpr)

  /-- checkers need not bother with conclusion of constructor,
      only hypotheses need be checked and conclusion of constructor follows-/
  | CheckerSchedule

  /-- In a `TheoremSchedule`, we check the `conclusion` of the theorem, and take in a `Bool`
      which is true if we need to find a checker by identifying the `DecOpt` instance,
      and false otherwise (we're currently dealing with a functino that returns `Option Bool`) -/
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



----------------------------------------------
-- Conversion from `Expr` to `HypothesisExpr`
----------------------------------------------


/-- Convert an `Expr` to a `ConstructorExpr` -/
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
  -- Only proceed if `ctorName` is actually a constructor
  if env.isConstructor ctorName then
    let constructorArgs ← args.mapM exprToConstructorExpr
    return some (ctorName, constructorArgs.toList)
  else
    return none
