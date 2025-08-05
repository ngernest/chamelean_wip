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
import Plausible.IR.Prelude
import Plausible.IR.Examples

import Plausible.New.Arbitrary
import Plausible.New.STLC

import Lean.Elab.Command
import Lean.Meta.Basic

open Lean Elab Command Meta Term Parser
open Idents
open Plausible.IR

---------------------------------------------------------------------------------------------
-- Implements figure 4 from "Generating Good Generators for Inductive Relations" (GGG), POPL '18
--------------------------------------------------------------------------------------------

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

/-- Converts an `Expr` to a `Range`, using the ambient `LocalContext` to find the user-facing names
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

mutual

  /-- Produces the code for a pattern match on an unknown
     TODO: split this into 2 steps
     1. Compile a `ScheduleStep` to an `MExp`
     2. Compile the `MExp` to a Lean term

   -/
  partial def emitPatterns (patterns : List (Unknown × Pattern)) (equalities : List (Unknown × Unknown)) (constraints : UnknownMap) : UnifyM (TSyntax `term) :=
    match patterns with
    | [] => emitEqualities equalities constraints
    | (u, p) :: ps => do
      let caseRHS ← emitPatterns ps equalities constraints
      let caseLHS ← convertPatternToTerm p

      -- If the pattern-match succeeds, use the RHS computed in `caseRHS`
      let nonTrivialCase ← `(Term.matchAltExpr| | $caseLHS => $caseRHS)

      -- Otherwise, just return `None` (by doing `OptionT.fail`)
      let trivialCase ← `(Term.matchAltExpr| | _ => $failFn)

      -- Create the actual pattern-match
      let cases := #[nonTrivialCase, trivialCase]
      mkMatchExpr (mkIdent u) cases

  /-- Produces the code for an equality check according to a list of `equalities` and a particular set of `constraints` -/
  partial def emitEqualities (equalities : List (Unknown × Unknown)) (constraints : UnknownMap) : UnifyM (TSyntax `term) :=
    match equalities with
    | [] => UnifyM.withHypotheses (fun hyps => emitHypotheses hyps constraints)
    | (u1, u2) :: eqs => do
      /- We produce the expression
        ```lean
        match DecOpt.decOpt ($u1 = $u2) $initSize with
        | some true => $trueCaseRHS
        | _ => OptionT.fail
        ```
        where we invoke the checker provided by the `DecOpt` typeclass to determine whether `u1 = u2` -/

      let scrutinee ← `($decOptFn ($(mkIdent u1) == $(mkIdent u2)) $initSizeIdent)
      let trueCaseRHS ← emitEqualities eqs constraints
      let trueCase ← `(Term.matchAltExpr | | $(mkIdent ``some) $(mkIdent ``true) => $trueCaseRHS)
      let catchAllCase ← `(Term.matchAltExpr | | _ => $failFn)
      let cases := #[trueCase, catchAllCase]
      mkMatchExprWithScrutineeTerm scrutinee cases

  /-- Determines if all unknowns in a `ConstructorExpr` have `Range`s of the form `Undef τ` for some type `τ` -/
  partial def allUnknownsHaveUndefRanges (ctorExpr : ConstructorExpr) : UnifyM Bool := do
    logWarning m!"Checking if unknowns in {ctorExpr} have Undef Ranges"
    match ctorExpr with
    | .Unknown u => not <$> UnifyM.hasUndefRange u
    | .Ctor _ args =>
      logWarning m!"entered Ctor case of allUnknownsHaveUndefRanges with {ctorExpr}"
      List.allM allUnknownsHaveUndefRanges args

  /-- Produces the code for the body of a sub-generator which processes a list of `hypotheses` under a particular set of `constraints`

    - Note: `emitHypotheses` combines the checker/producer `ScheduleStep`s into one function
    - One option if we want to keep `emitHypotheses` is compile `ScheduleStep`s to `HypothesisExpr`s,
      i.e. `Name × List ConstructorExpr`
      +
    - However, it might be cleaner if we rip out all the emit functions, and go directly
      from `ScheduleStep`s to `MExp`s, then from `MExp` to Lean code

  -/
  partial def emitHypotheses (hypotheses : List (Name × List ConstructorExpr)) (constraints : UnknownMap) : UnifyM (TSyntax `term) := do
    match hypotheses with
    | [] => finalAssembly
    | hypothesis@(ctorName, ctorArgs) :: remainingHyps => do
      logWarning m!"inEmitHypotheses, head of list is ({ctorName} {ctorArgs})"
      /- If all of the constructor's args don't have a `Range` of the form `Undef τ`,
        we can simply produce the expression
        ```lean
        match DecOpt.decOpt ($ctorName $ctorArgs*) with
        | some true => $(emitHypotheses hyps constrains)
        | _ => OptionT.fail
        ```
        where we invoke the checker for the hypothesis and pattern-match based on its result -/
      if (← List.allM allUnknownsHaveUndefRanges ctorArgs) then
        logWarning m!"emitHypotheses ({ctorName} {ctorArgs}), all unknowns don't have Undef range"
        let ctorArgsArr ← UnifyM.convertConstructorExprsToTSyntaxTerms ctorArgs.toArray
        let hypothesisCheck ← `($decOptFn ($(mkIdent ctorName) $ctorArgsArr*) $initSizeIdent)
        let trueCaseRHS ← emitHypotheses remainingHyps constraints
        let trueCase ← `(Term.matchAltExpr| | $(mkIdent ``some) $(mkIdent ``true) => $trueCaseRHS)
        let catchAllCase ← `(Term.matchAltExpr| | _ => $failFn)
        let cases := #[trueCase, catchAllCase]
        mkMatchExprWithScrutineeTerm hypothesisCheck cases
      else
        let mut doElems := #[]

        -- Accumulate all unknowns contained in `ctorArgs`
        let unknownsInCtorArgs ← List.flatMapM UnifyM.collectUnknownsInConstructorExpr ctorArgs
        -- `undefUnknowns` is a list of all `Unknown`s in `ctorArgs` that have a `Range` of the form `Undef τ`, with length `n`
        let undefUnknowns ← UnifyM.findUnknownsWithUndefRanges unknownsInCtorArgs

        logWarning m!"emitHypotheses ({ctorName} {ctorArgs}), unknowns {undefUnknowns} have Undef range"

        match unsnoc undefUnknowns with
        | none => throwError "Unreachable case: by construction, there must exist at least one unknown with an `Undef` Range"
        | some (undefUnknownsPrefix, finalUnknown) =>
          -- For each `u ∈ undefUnknowns[0..=n-2]`, we generate `u` freely by producing the expr `let u ← arbitrary`
          for u in undefUnknownsPrefix do
            let letBindExpr ← mkLetBind (mkIdent u) #[arbitraryFn]
            doElems := doElems.push letBindExpr

          logWarning m!"finalUnknown = {finalUnknown}"

          -- To generate the `finalUnknown`, we pass the `finalUnknown` and the current `hypothesis` to `emitFinalCall`
          doElems := doElems.push (← emitFinalCall finalUnknown hypothesis)

          -- We then update all `u ∈ undefUnknowns` to have a fixed range in `constraints`,
          -- and handle the remaining hypotheses via a recursive call to `emitHypotheses` with the updated `constraints`
          UnifyM.fixRanges undefUnknowns
          let recursiveCallResult ← UnifyM.withConstraints (fun k => emitHypotheses remainingHyps k)
          doElems := doElems.push (← `(doElem| $recursiveCallResult:term))

          -- We then put everything together in one big monadic do-block
          mkDoBlock doElems

  /-- Assembles the body of the generator (this function is called when all hypotheses have been processed by `emitHypotheses`)

      (Note that this function doesn't take in an explicit `constraints` argument (unlike the pseudocode in the paper),
      since we fetch the `constraints` map via a `get` call in the State monad)

      - This corresponds to `finally` in QuickChick code
      -/
  partial def finalAssembly : UnifyM (TSyntax `term) := do
    -- Find all unknowns whose ranges are `Undef`
    let undefUnknowns ← UnifyM.withUnknowns (fun allUnknowns => UnifyM.findUnknownsWithUndefRanges allUnknowns.toList)

    -- Update the constraint map so that all unknowns in `undefKnowns` now have a `Fixed` `Range`
    UnifyM.fixRanges undefUnknowns

    -- Construct the final expression that will be produced by the generator
    let unifyState ← get
    let outputName := unifyState.outputName
    let updatedConstraints := unifyState.constraints
    let rangeForOutput ← UnifyM.findCorrespondingRange updatedConstraints outputName

    let result ← emitResult updatedConstraints outputName rangeForOutput

    -- Bind each unknown in `undefUnknowns` to the result of an arbitrary call,
    -- then return the value computed in `result`
    let mut doElems := #[]
    for u in undefUnknowns do
      doElems := doElems.push (← mkLetBind (mkIdent u) #[arbitraryFn])
    doElems := doElems.push (← `(doElem| return $result))

    -- Put everything together in one monadic do-block
    mkDoBlock doElems

  /-- Produces a let-bind expression which generates an `unknown` subject to a `hypothesis`
      in the body of the sub-generator
      (this is the final call to a generator when processing one particular hypothesis of a constructor)

      - Note: This handles any producer step in a schedule
      - Segev says "I would hesitate to use the same GGG algorithm as written" since
        it goes directly to Lean code, instead use `ScheduleStep`s, compile those to `MExp`, then
        compile those to `TSyntax`
  -/
  partial def emitFinalCall (unknown : Unknown) (hypothesis : Name × List ConstructorExpr): UnifyM (TSyntax `doElem) := do
    let unifyState ← get
    let outputName := unifyState.outputName
    let lhs := mkIdent unknown
    logWarning m!"inside emitFinalCall, unknown = {unknown}, outputName = {outputName}"

    -- Determine if a recursive call to `auxArb` is needed, i.e. if the `range` corresponding to `unknown`
    -- is `.Undef ty`, where `ty` is the same type as the `outputType` (with type equality determined by `Meta.isDefEq`)
    let range ← UnifyM.findCorrespondingRange unifyState.constraints unknown
    let recursiveCallNeeded ←
      (match range with
      | .Undef ty =>
        Meta.isDefEq ty unifyState.outputType
      | _ => pure false)

    logWarning m!"recursiveCallNeeded = {recursiveCallNeeded}"

    if unknown == outputName || recursiveCallNeeded then
      logWarning m!"entered true branch of emitFinalCall"

      -- Produce a recursive call to `auxArb` (recursively generate a value for the unknown)
      -- Each `input` in `inputNames` is an argument for `auxArb`
      let argsForRecursiveCall := Lean.mkIdent <$> unifyState.inputNames.toArray

      -- Produce a monadic let-bind expression of the form `let $lhs ← auxArb initSize size' $argsForRecursiveCall`
      mkLetBind lhs (#[auxArbFn, initSizeIdent, mkIdent `size'] ++ argsForRecursiveCall)
    else do
      -- Generate a value for the unknown via a call to `arbitraryST`, passing in the final hypothesis
      -- as an argument to `arbitraryST`
      let unknownIdent := mkIdent unknown
      let (ctorName, ctorArgs) := hypothesis
      let ctorArgsArr ← UnifyM.convertConstructorExprsToTSyntaxTerms ctorArgs.toArray
      let constraint ← `((fun $unknownIdent => $(mkIdent ctorName) $ctorArgsArr*))
      let rhsTerms := #[(arbitrarySTFn : TSyntax `term), constraint]
      mkLetBind lhs rhsTerms

  /-- Produces a term corresponding to the value being generated -/
  partial def emitResult (k : UnknownMap) (u : Unknown) (range : Range) : UnifyM (TSyntax `term) := do
    match range with
    | .Unknown u' => emitResult k u' (← UnifyM.findCorrespondingRange k u')
    | .Fixed => `($(mkIdent u))
    | .Ctor c rs => do
      let ctorIdent := mkIdent c
      let ctorArgs ← Array.mapM (fun r => emitResult k u r) rs.toArray
      `($ctorIdent $ctorArgs*)
    | .Undef ty => throwError m!"Error: unknown {u} has a range of (Undef {ty}) in {k.toList}"

end

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
    - The constructor name `ctorName`
    - The name (`outputName`) and type (`outputType`) of the output (value to be generated)
    - The names of inputs `inputNames` (arguments to the generator)
    - An array of `unknowns` (the arguments to the inductive relation)
      + Note: `unknowns == inputNames ∪ { outputName }`, i.e. `unknowns` contains all args to the inductive relation
        listed in order, which coincides with `inputNames ∪ { outputName }`
    - The name of the inductive relation we are targeting (`inductiveName`) -/
def getScheduleForConstructor (ctorName : Name) (outputName : Name) (outputType : Expr) (inputNames : List Name)
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
      let hypTerm ← delabExprInLocalContext localCtx hyp
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
      (recCall := (`typing, [outputIdx]))
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


/-- Command for deriving a sub-generator for one construtctor of an inductive relation (per figure 4 of GGG) -/
syntax (name := derive_subgenerator) "#derive_subgenerator" "(" "fun" "(" ident ":" term ")" "=>" term ")" : command

@[command_elab derive_subgenerator]
def elabDeriveSubGenerator : CommandElab := fun stx => do
  match stx with
  | `(#derive_subgenerator ( fun ( $var:ident : $outputTypeSyntax:term ) => $body:term )) => do

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

        for ctorName in inductiveVal.ctors do
          let scheduleOption ← (UnifyM.runInMetaM
            (getScheduleForConstructor ctorName freshenedOutputName
              outputType freshenedInputNamesExcludingOutput freshUnknowns)
              emptyUnifyState)
          match scheduleOption with
          | some schedule =>
            -- Compile the schedule to an `MExp`, then compile the `MExp` to a Lean term containing the code for the sub-generator
            let mexp ← scheduleToMExp schedule (.MId `size) (.MId `initSize)
            let subGenerator ← mexpToTSyntax mexp .Generator
            -- logInfo m!"Derived generator:\n```\n{subGenerator}\n```"

            -- Determine whether the constructor is recursive
            -- (i.e. if the constructor has a hypothesis that refers to the inductive relation we are targeting)
            let isRecursive ← isConstructorRecursive inductiveName ctorName

            if isRecursive then
              weightedRecursiveGenerators := weightedRecursiveGenerators.push (← `( ($(mkIdent ``Nat.succ) $freshSize', $subGenerator) ))
            else
              weightedNonRecursiveGenerators := weightedNonRecursiveGenerators.push (← `( (1, $subGenerator) ))

          | none => throwError m!"Unable to derive generator schedule for constructor {ctorName}"

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
    -- & prompt the user to accept it in the VS Code side panel
    liftTermElabM $ Tactic.TryThis.addSuggestion stx
      (Format.pretty genFormat) (header := "Try this generator: ")

    elabCommand typeClassInstance

  | _ => throwUnsupportedSyntax


-- Extra Arbitrary instances needed in order for STLC example to work
deriving instance Arbitrary for type, term

-- Extra `ArbitrarySizedSuchThat` needed in order for STLC example to work
instance : ArbitrarySizedSuchThat type (fun t => typing G e t) where
  arbitrarySizedST := sorry


-- #derive_subgenerator (fun (tree : Tree) => bst in1 in2 tree)
-- #derive_subgenerator (fun (e : term) => typing G e t)

-- #derive_subgenerator (fun (tree : Tree) => LeftLeaning tree)

-- #derive_subgenerator (fun (xs : List Nat) => Sorted xs)
