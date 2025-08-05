import Lean.Expr
import Lean.LocalContext

import Plausible.GeneratingGoodGenerators.UnificationMonad
import Plausible.GeneratingGoodGenerators.Schedules
import Plausible.GeneratingGoodGenerators.ScheduleUtils
import Plausible.GeneratingGoodGenerators.MExp
import Plausible.New.DeriveConstrainedProducers
import Plausible.New.SubGenerators
import Plausible.New.DeriveArbitrary
import Plausible.New.TSyntaxCombinators
import Plausible.New.Utils
import Plausible.New.Debug
import Plausible.IR.Prelude
import Plausible.IR.Examples

import Plausible.New.Arbitrary
import Plausible.New.STLC

import Lean.Elab.Command
import Lean.Meta.Basic

open Lean Elab Command Meta Term Parser
open Idents
open Plausible.IR

----------------------------------------------------------------------------------------------------------------------------------
-- Adapted from "Generating Good Generators for Inductive Relations" (POPL '18) & "Testing Theorems, Fully Automatically" (2025)
----------------------------------------------------------------------------------------------------------------------------------

/-- Creates the initial constraint map κ where all inputs are `Fixed`, the output & all universally-quantified variables is `Undef`
    - `forAllVariables` is a list of (variable name, variable type) pairs -/
def mkInitialUnknownMap (inputNames: List Name) (outputName : Name) (outputType : Expr) (forAllVariables : List (Name × Expr)) : UnknownMap :=
  let inputConstraints := inputNames.zip (List.replicate inputNames.length .Fixed)
  let outputConstraints := [(outputName, .Undef outputType)]
  let filteredForAllVariables := forAllVariables.filter (fun (x, _) => x ∉ inputNames)
  let forAllVarsConstraints := (fun (x, ty) => (x, .Undef ty)) <$> filteredForAllVariables
  Std.HashMap.ofList $ inputConstraints ++ outputConstraints ++ forAllVarsConstraints

/-- Creates the initial `UnifyState` corresponding to a constructor of an inductive relation
   - `inputNames`: the names of all inputs to the generator
   - `outputName`, `outputType`: name & type of the output (variable to be generated)
   - `forAllVariables`: the names & types for universally-quantified variables in the constructor's type
   - `hypotheses`: the hypotheses for the constructor (represented as a constructor name applied to some list of arguments) -/
def mkInitialUnifyState (inputNames : List Name) (outputName : Name) (outputType : Expr) (forAllVariables : List (Name × Expr))
  (hypotheses : List (Name × List ConstructorExpr)): UnifyState :=
  let forAllVarNames := Prod.fst <$> forAllVariables
  let constraints := mkInitialUnknownMap inputNames outputName outputType forAllVariables
  let unknowns := Std.HashSet.ofList (outputName :: (inputNames ++ forAllVarNames))
  { constraints := constraints
    equalities := ∅
    patterns := []
    unknowns := unknowns
    outputName := outputName
    outputType := outputType
    inputNames := inputNames
    hypotheses := hypotheses }

/-- Converts a expression `e` to a *constructor expression* `C r1 … rn`,
    where `C` is a constructor and the `ri` are arguments,
    returning `some (C, #[r1, …, rn])`
    - If `e` is not an application, this function returns `none`  -/
def convertToCtorExpr (e : Expr) : MetaM (Option (Name × Array Expr)) :=
  if e.isConst then
    -- Nullary constructors are identified by name
    return some (e.constName!, #[])
  else if e.isApp then do
    -- Constructors with arguments
    let (ctorName, args) := e.getAppFnArgs
    let mut actualArgs := #[]
    for arg in args do
      -- Figure out whether `argType` is `Type u` for some universe `u`
      let argType ← inferType arg
      -- If `argType` is `Type u` or `Sort u`, then we know `arg` itself must be a type
      -- (i.e. it is part of an explicit type application), so we can omit it from `actualArgs`
      if argType.isSort then
        continue
      else if argType.isApp then
        -- Handle case where `argType` is a typeclass instance
        -- (e.g. `LT Nat` is supplied as an argument to `<`)
        -- Typeclass instance arguments which are explicit type applications
        -- can be omitted from `actualArgs`
        let (typeCtorName, _) := argType.getAppFnArgs
        let env ← getEnv
        if Lean.isClass env typeCtorName then
          continue
        else
          actualArgs := actualArgs.push arg
      else
        actualArgs := actualArgs.push arg
    return some (ctorName, actualArgs)
  else
    return none



/-- Takes an unknown `u`, and finds the `Range` `r` that corresponds to
    `u` in the `constraints` map.

    However, there are 3 conditions in which we generate a fresh unknown `u'`
    and update the `constraints` map with the binding `u' ↦ Unknown u`:

    1. `u` isn't present in the `constraints` map (i.e. no such `r` exists)
    2. `r = .Fixed`
    3. `r = .Undef τ` for some type τ
    (We need to hand latter two conditions are )

    We need to handle conditions (2) and (3) because the top-level ranges
    passed to `UnifyM.unify` cannot be `Fixed` or `Undef`, as stipulated
    in the QuickChick codebase / the Generating Good Generators paper. -/
def processCorrespondingRange (u : Unknown) : UnifyM Range :=
  UnifyM.withConstraints $ fun k =>
    match k[u]? with
    | some .Fixed | some (.Undef _) | none => do
      let u' ← UnifyM.registerFreshUnknown
      UnifyM.update u' (.Unknown u)
      return .Unknown u'
    | some r => return r

/-- Converts an `Expr` to a `Range`, using the `LocalContext` to find the user-facing names
    corresponding to `FVarId`s -/
partial def convertExprToRangeInCurrentContext (e : Expr) : UnifyM Range := do
  match (← convertToCtorExpr e) with
  | some (f, args) => do
    let argRanges ← args.toList.mapM convertExprToRangeInCurrentContext
    return (Range.Ctor f argRanges)
  | none =>
    if e.isFVar then do
      let localCtx ← getLCtx
      match localCtx.findFVar? e with
      | some localDecl =>
        let u := localDecl.userName
        return (.Unknown u)
      | none =>
        let namesInContext := (fun e => getUserNameInContext! localCtx e.fvarId!) <$> localCtx.getFVars
        throwError m!"{e} missing from LocalContext, which only contains {namesInContext}"
    else
      match e with
      | .const u _ => return (.Unknown u)
      | .lit literal =>
        -- Nat / String literals correspond to a `Range` that is a nullary constructor
        let name :=
          match literal with
          | .natVal n => Name.mkStr1 (toString n)
          | .strVal s => Name.mkStr1 s
        return .Ctor name []
      | _ => throwError m!"Cannot convert expression {e} to Range"

/-- Converts a hypothesis (reprented as a `TSyntax term`) to a `Range` -/
partial def convertHypothesisTermToRange (term : TSyntax `term) : UnifyM Range := do
  match term with
  | `($ctor:ident $args:term*) => do
    let argRanges ← Array.toList <$> args.mapM convertHypothesisTermToRange
    return (.Ctor ctor.getId argRanges)
  | `($ctor:ident) =>
    -- Use `getConstInfo` to determine if the identifier is a variable name or
    -- a nullary constructor of an inductive type
    let name := ctor.getId
    let constInfo ← getConstInfo name
    if constInfo.isCtor then
      return (Range.Ctor name [])
    else
      return (.Unknown name)
  | _ => throwError m!"unable to convert {term} to a Range"

/-- Converts a `Pattern` to a `TSyntax term` -/
def convertPatternToTerm (pattern : Pattern) : MetaM (TSyntax `term) :=
  match pattern with
  | .UnknownPattern name => return (mkIdent name)
  | .CtorPattern ctorName args => do
    let ctorIdent := mkIdent ctorName
    let argSyntaxes ← args.mapM convertPatternToTerm
    argSyntaxes.foldlM (fun acc arg => `($acc $arg)) ctorIdent


/-- Converts a `Range` to a `ConstructorExpr`
    (helper function used by `convertRangeToCtorAppForm`) -/
partial def convertRangeToConstructorExpr (r : Range) : UnifyM ConstructorExpr :=
  match r with
  | .Unknown u => return (.Unknown u)
  | .Ctor ctorName args => do
    let updatedArgs ← args.mapM convertRangeToConstructorExpr
    return (.Ctor ctorName updatedArgs)
  | _ => throwError m!"Unable to convert {r} to a constructor expression"

/-- Converts a `Range` that is either an `Unknown` or `Ctor` to
    a term in *constructor application form*, represented as a pair of type `(Name × List ConstructorExpr)`
    (constructor name applied to zero or more arguments which may themselves be `ConstructorExpr`s) -/
def convertRangeToCtorAppForm (r : Range) : UnifyM (Name × List ConstructorExpr) :=
  match r with
  | Range.Unknown u => return (u, [])
  | Range.Ctor c rs => do
    let args ← rs.mapM convertRangeToConstructorExpr
    return (c, args)
  | _ => throwError m!"Unable to convert {r} to a constructor expression"

/-- Given a `conclusion` to a constructor, a list of `outputVars` and a `deriveSort`,
    figures out the appropriate `ScheduleSort`. The `returnOption` boolean argument
    is used to determine whether producers should return their results wrapped in an `Option` or not.

    - Note: callers should supply `none` as the `ctorNameOpt` argument if `deriveSort := .Theorem` -/
def getScheduleSort (conclusion : HypothesisExpr) (outputVars : List Unknown) (ctorNameOpt : Option Name) (deriveSort : DeriveSort) (returnOption : Bool) : UnifyM ScheduleSort :=
  match deriveSort with
  | .Checker => return .CheckerSchedule
  | .Theorem => return (.TheoremSchedule conclusion (typeClassUsed := true))
  | _ => do
    let outputValues ← outputVars.mapM UnifyM.evaluateUnknown
    let producerSort :=
      if let .Enumerator := deriveSort then ProducerSort.Enumerator
      else ProducerSort.Generator
    let conclusion ← do
      if returnOption then
        pure outputValues
      else
        let ctorName ← Option.getDM ctorNameOpt
          (throwError "No constructor name given for Non-theorem schedule")
        pure [ConstructorExpr.Ctor ctorName outputValues]
    -- TODO: fix this (we shouldn't return the conclusion as is)
    return .ProducerSchedule producerSort conclusion


/-- Computes a *naive* generator schedule for a sub-generator corresponding to a constructor of an inductive relation.
    Note: this function processes the entire type of the constructor within the same `LocalContext`
    (the one produced by `forallTelescopeReducing`).

    This function takes the following as arguments:
    - The name of the inductive relation `inductiveName`
    - The constructor name `ctorName`
    - The name (`outputName`) and type (`outputType`) of the output (value to be generated)
    - The names of inputs `inputNames` (arguments to the generator)
    - An array of `unknowns` (the arguments to the inductive relation)
      + Note: `unknowns == inputNames ∪ { outputName }`, i.e. `unknowns` contains all args to the inductive relation
        listed in order, which coincides with `inputNames ∪ { outputName }`
    - The name of the inductive relation we are targeting (`inductiveName`) -/
def getScheduleForConstructor (inductiveName : Name) (ctorName : Name) (outputName : Name) (outputType : Expr) (inputNames : List Name)
  (unknowns : Array Unknown) : UnifyM Schedule := do
  let ctorInfo ← getConstInfoCtor ctorName
  let ctorType := ctorInfo.type

  -- Stay within the forallTelescope scope for all processing
  forallTelescopeReducing ctorType (cleanupAnnotations := true) (fun forAllVarsAndHyps conclusion => do
    -- Universally-quantified variables `x : τ` are represented using `(some x, τ)`
    -- Hypotheses are represented using `(none, hyp)` (first component is `none` since a hypothesis doesn't have a name)
    let forAllVarsAndHypsWithTypes ← forAllVarsAndHyps.mapM (fun fvar => do
      let localCtx ← getLCtx
      let localDecl := localCtx.get! fvar.fvarId!
      let userName := localDecl.userName
      if not userName.hasMacroScopes then
        return (some userName, localDecl.type)
      else
        return (none, localDecl.type))

    let forAllVars := forAllVarsAndHypsWithTypes.filterMap (fun (nameOpt, ty) =>
      match nameOpt with
      | some name => (name, ty)
      | none => none) |>.toList

    -- Extract hypotheses (which correspond to pairs in `forAllVarsAndHypsWithTypes` where the first component is `none`)
    let hypotheses := forAllVarsAndHypsWithTypes.filterMap (fun (nameOpt, tyExpr) =>
      match nameOpt with
      | none => tyExpr
      | some _ => none)
    let localCtx ← getLCtx

    -- Stores the representation of hypotheses as a `HypothesisExpr`
    -- (constructor name applied to some list of arguments, which are themselves `ConstructorExpr`s)
    let mut hypothesisExprs := #[]

    for hyp in hypotheses do
      let hypTerm ← withOptions setDelaboratorOptions (delabExprInLocalContext localCtx hyp)
      -- Convert the `TSyntax` representation of the hypothesis to a `Range`
      -- If that fails, convert the `Expr` representation of the hypothesis to a `Range`
      -- (the latter is needed to handle hypotheses which use infix operators)
      let hypRange ←
        try convertHypothesisTermToRange hypTerm
        catch _ => convertExprToRangeInCurrentContext hyp

      -- Convert each hypothesis' range to a `HypothesisExpr`, which is just a constructor application
      -- (constructor name applied to some list of arguments, which are themselves `ConstructorExpr`s)
      hypothesisExprs := hypothesisExprs.push (← convertRangeToCtorAppForm hypRange)

    -- Creates the initial `UnifyState` needed for the unification algorithm
    let initialUnifyState := mkInitialUnifyState inputNames outputName outputType forAllVars hypothesisExprs.toList

    -- Extend the current state with the contents of `initialUnifyState`
    UnifyM.extendState initialUnifyState

    -- Get the ranges corresponding to each of the unknowns
    let unknownRanges ← unknowns.mapM processCorrespondingRange
    let unknownArgsAndRanges := unknowns.zip unknownRanges

    -- Compute the appropriate `Range` for each argument in the constructor's conclusion
    let conclusionArgs := conclusion.getAppArgs
    let conclusionRanges ← conclusionArgs.mapM convertExprToRangeInCurrentContext
    let conclusionArgsAndRanges := conclusionArgs.zip conclusionRanges

    for ((_u1, r1), (_u2, r2)) in conclusionArgsAndRanges.zip unknownArgsAndRanges do
      unify r1 r2

    -- Convert the conclusion from an `Expr` to a `HypothesisExpr`
    let conclusionExpr ← Option.getDM (← exprToHypothesisExpr conclusion)
      (throwError m!"Unable to convert {conclusion} to a HypothesisExpr")

    -- Determine the appropriate `ScheduleSort` (right now we only produce `ScheduleSort`s for `Generator`s)
    let scheduleSort ← getScheduleSort conclusionExpr
      (outputVars := [outputName]) (some ctorName) (deriveSort := .Generator)
      (returnOption := true)

    -- Check which universally-quantified variables have a `Fixed` range,
    -- so that we can supply them to `possibleSchedules` as the `fixedVars` arg
    let fixedVars ← forAllVars.filterMapM (fun (v, _) => do
      if (← UnifyM.isUnknownFixed v) then
        return some v
      else
        return none)

    let outputIdx := unknowns.idxOf outputName

    -- Compute all possible generator schedules for this constructor
    let possibleSchedules ← possibleSchedules
      (vars := forAllVars)
      (hypotheses := hypothesisExprs.toList)
      (deriveSort := .Generator)
      (recCall := (inductiveName, [outputIdx]))
      fixedVars

    -- A *naive* schedule is the first schedule contained in `possibleSchedules`
    let originalNaiveSchedule ← Option.getDM (possibleSchedules.head?) (throwError m!"Unable to compute any possible schedules")

    -- Update the naive schedule with the result of unification
    let updatedNaiveSchedule ← updateScheduleSteps originalNaiveSchedule

    let finalState ← get

    -- Takes the `patterns` and `equalities` fields from `UnifyState` (created after
    -- the conclusion of a constructor has been unified with the top-level arguments to the inductive relation),
    -- convert them to the appropriate `ScheduleStep`s, and prepends them to the `naiveSchedule`
    let fullSchedule := addConclusionPatternsAndEqualitiesToSchedule finalState.patterns finalState.equalities (updatedNaiveSchedule, scheduleSort)

    return fullSchedule)


/-- Command for deriving a constrained generator for an inductive relation that uses generator schedules -/
syntax (name := derive_scheduled_generator) "#derive_scheduled_generator" "(" "fun" "(" ident ":" term ")" "=>" term ")" : command

/-- Elaborator for the `#derive_scheduled_generator` command which derives constrained generator using generator schedules -/
@[command_elab derive_scheduled_generator]
def elabDeriveScheduledGenerator : CommandElab := fun stx => do
  match stx with
  | `(#derive_scheduled_generator ( fun ( $var:ident : $outputTypeSyntax:term ) => $body:term )) => do

    -- Parse the body of the lambda for an application of the inductive relation
    let (inductiveSyntax, argIdents) ← parseInductiveApp body
    let inductiveName := inductiveSyntax.getId

    -- Figure out the name and type of the value we wish to generate (the "output")
    let outputName := var.getId
    let outputType ← liftTermElabM $ elabTerm outputTypeSyntax none

    -- Find the index of the argument in the inductive application for the value we wish to generate
    -- (i.e. find `i` s.t. `argIdents[i] == outputName`)
    let outputIdxOpt := findTargetVarIndex outputName argIdents
    if let .none := outputIdxOpt then
      throwError "cannot find index of value to be generated"
    let outputIdx := Option.get! outputIdxOpt

    -- Obtain Lean's `InductiveVal` data structure, which contains metadata about the inductive relation
    let inductiveVal ← getConstInfoInduct inductiveName

    -- Determine the type for each argument to the inductive
    let (_, _, inductiveTypeComponents) ← liftTermElabM $ decomposeType inductiveVal.type

    -- To obtain the type of each arg to the inductive,
    -- we pop the last element (`Prop`) from `inductiveTypeComponents`
    let argTypes := inductiveTypeComponents.pop
    let argNames := (fun ident => ident.getId) <$> argIdents
    let argNamesTypes := argNames.zip argTypes

    -- Add the name & type of each argument to the inductive relation to the ambient `LocalContext`
    -- (as a local declaration)
    let (baseGenerators, inductiveGenerators, freshenedOutputName, freshArgIdents, localCtx) ←
      liftTermElabM $ withLocalDeclsDND argNamesTypes (fun _ => do
        let mut localCtx ← getLCtx
        let mut freshUnknowns := #[]

        -- For each arg to the inductive relation (as specified to the user),
        -- create a fresh name (to avoid clashing with names that may appear in constructors
        -- of the inductive relation). Note that this requires updating the `LocalContext`
        for argName in argNames do
          let freshArgName := localCtx.getUnusedName argName
          localCtx := localCtx.renameUserName argName freshArgName
          freshUnknowns := freshUnknowns.push freshArgName

        -- Since the `output` also appears as an argument to the inductive relation,
        -- we also need to freshen its name
        let freshenedOutputName := freshUnknowns[outputIdx]!

        -- Each argument to the inductive relation (except the one at `outputIdx`)
        -- is treated as an input
        let freshenedInputNamesExcludingOutput := (Array.eraseIdx! freshUnknowns outputIdx).toList

        let mut weightedNonRecursiveGenerators := #[]
        let mut weightedRecursiveGenerators := #[]

        let freshSize' := mkIdent $ localCtx.getUnusedName `size'

        let mut requiredInstances := #[]

        for ctorName in inductiveVal.ctors do
          let scheduleOption ← (UnifyM.runInMetaM
            (getScheduleForConstructor inductiveName ctorName freshenedOutputName
              outputType freshenedInputNamesExcludingOutput freshUnknowns)
              emptyUnifyState)
          match scheduleOption with
          | some schedule =>
            -- Obtain a sub-generator for this constructor, along with an array of all typeclass instances that need to be defined beforehand
            -- (Under the hood, we compile the schedule to an `MExp`, then compile the `MExp` to a Lean term containing the code for the sub-generator.
            -- This is all done in a state monad, where we keep appending to an array of typeclass instance names when we detect that a new instance is required)
            let (subGenerator, instances) ← StateT.run (s := #[]) (do
              let mexp ← scheduleToMExp schedule (.MId `size) (.MId `initSize)
              mexpToTSyntax mexp .Generator)

            requiredInstances := requiredInstances ++ instances

            -- Determine whether the constructor is recursive
            -- (i.e. if the constructor has a hypothesis that refers to the inductive relation we are targeting)
            let isRecursive ← isConstructorRecursive inductiveName ctorName

            if isRecursive then
              weightedRecursiveGenerators := weightedRecursiveGenerators.push (← `( ($(mkIdent ``Nat.succ) $freshSize', $subGenerator) ))
            else
              weightedNonRecursiveGenerators := weightedNonRecursiveGenerators.push (← `( (1, $subGenerator) ))

          | none => throwError m!"Unable to derive generator schedule for constructor {ctorName}"

        if (not requiredInstances.isEmpty) then
          let deduplicatedInstances := List.eraseDups requiredInstances.toList
          logWarning m!"Required typeclass instances (please derive these first if they aren't already defined):\n{deduplicatedInstances}"

        let baseGenerators ← `([$weightedNonRecursiveGenerators,*])
        let inductiveGenerators ← `([$weightedNonRecursiveGenerators,*, $weightedRecursiveGenerators,*])

        return (baseGenerators, inductiveGenerators, freshenedOutputName, Lean.mkIdent <$> freshUnknowns, localCtx))

    -- Create an instance of the `ArbitrarySuchThat` typeclass
    let typeClassInstance ←
      mkProducerTypeClassInstance'
        baseGenerators inductiveGenerators
        inductiveSyntax freshArgIdents
        freshenedOutputName outputTypeSyntax
        .Generator localCtx

    -- Pretty-print the derived generator
    let genFormat ← liftCoreM (PrettyPrinter.ppCommand typeClassInstance)

    -- Display the code for the derived generator to the user
    logInfo m!"Try this generator: {Format.pretty genFormat}"

    -- Display the code for the derived generator to the user
    -- & prompt the user to accept it in the VS Code side panel
    -- liftTermElabM $ Tactic.TryThis.addSuggestion stx
    --   (Format.pretty genFormat) (header := "Try this generator: ")

    elabCommand typeClassInstance

  | _ => throwUnsupportedSyntax

-- TODO: debug these cases
-- #derive_scheduled_generator (fun (l : List Nat) => inList x l)
