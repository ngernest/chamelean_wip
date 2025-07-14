import Lean
import Std
import Batteries

import Plausible.GeneratingGoodGenerators.UnificationMonad
import Plausible.New.DeriveConstrainedProducers
import Plausible.New.SubGenerators
import Plausible.New.DeriveArbitrary
import Plausible.New.TSyntaxCombinators
import Plausible.New.Debug
import Plausible.New.Utils
import Plausible.IR.Prelude
import Plausible.IR.Examples


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

/-- Creates the initial `UnifyState` where the constraint map is created using `mkInitialUnknownMap` -/
def mkInitialUnifyState (inputNames : List Name) (outputName : Name) (outputType : Expr) (forAllVariables : List (Name × Expr)) : UnifyState :=
  let forAllVarNames := Prod.fst <$> forAllVariables
  let constraints := mkInitialUnknownMap inputNames outputName outputType forAllVariables
  let unknowns := Std.HashSet.ofList (outputName :: (inputNames ++ forAllVarNames))
  -- TODO: fill in `hypotheses` here
  { constraints := constraints
    equalities := ∅
    patterns := []
    unknowns := unknowns
    outputName := outputName,
    hypotheses := [] }

/-- Converts a expression `e` to a *constructor expression* `C r1 … rn`,
    where `C` is a constructor and the `ri` are arguments,
    returning `some (C, #[r1, …, rn])`
    - If `e` is not an application, this function returns `none`  -/
def convertToCtorExpr (e : Expr) : Option (Name × Array Expr) :=
  if e.isConst then
    -- Nullary constructors are identified by name
    some (e.constName!, #[])
  else if e.isApp then
    -- Constructors with arguments
    some e.getAppFnArgs
  else none

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
partial def convertExprToRangeInCurrentContext (e : Expr) : UnifyM Range :=
  match convertToCtorExpr e with
  | some (f, args) => do
    let argRanges ← args.toList.mapM convertExprToRangeInCurrentContext
    return (Range.Ctor f argRanges)
  | none =>
    if e.isFVar then do
      let localCtx ← getLCtx
      match localCtx.findFVar? e with
      | some localDecl =>
        let u := localDecl.userName
        processCorrespondingRange u
      | none =>
        let namesInContext := (fun e => getUserNameInContext! localCtx e.fvarId!) <$> localCtx.getFVars
        throwError m!"{e} missing from LocalContext, which only contains {namesInContext}"
    else
      match e with
      | .const u _ => processCorrespondingRange u
      | _ => throwError m!"Cannot convert expression {e} to Range"

/-- Converts a `Pattern` to a `TSyntax term` -/
def convertPatternToTerm (pattern : Pattern) : MetaM (TSyntax `term) :=
  match pattern with
  | .UnknownPattern name => return (mkIdent name)
  | .CtorPattern ctorName args => do
    let ctorSyntax := mkIdent ctorName
    let argSyntaxes ← args.mapM convertPatternToTerm
    argSyntaxes.foldlM (fun acc arg => `($acc $arg)) ctorSyntax

mutual

  /-- Produces the code for a pattern match on an unknown -/
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

  /-- Produces the code for an equality check -/
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

  /-- Produces the code for the body of a sub-generator which processes hypotheses -/
  partial def emitHypotheses (hypotheses : List (Name × List Unknown)) (constraints : UnknownMap) : UnifyM (TSyntax `term) :=
    match hypotheses with
    | [] => finalAssembly
    | (ctorName, ctorArgs) :: remainingHyps => do
      /- If all of the constructor's args don't have a `Range` of the form `Undef τ`,
        we can simply produce the expression
        ```lean
        match DecOpt.decOpt ($ctorName $ctorArgs*) with
        | some true => $(emitHypotheses hyps constrains)
        | _ => OptionT.fail
        ```
        where we invoke the checker for the hypothesis and pattern-match based on its result -/
      if (← List.allM (fun u => not <$> UnifyM.hasUndefRange u) ctorArgs) then
        let ctorArgsArr := Lean.mkIdent <$> ctorArgs.toArray
        let hypothesisCheck ← `($decOptFn ($(mkIdent ctorName) $ctorArgsArr*) $initSizeIdent)
        let trueCaseRHS ← emitHypotheses remainingHyps constraints
        let trueCase ← `(Term.matchAltExpr| | $(mkIdent ``some) $(mkIdent ``true) => $trueCaseRHS)
        let catchAllCase ← `(Term.matchAltExpr| | _ => $failFn)
        let cases := #[trueCase, catchAllCase]
        mkMatchExprWithScrutineeTerm hypothesisCheck cases
      else
        let mut doElems := #[]

        -- `undefUnknowns` is a list of all `Unknown`s that have a `Range` of the form `Undef τ`, with length `n`
        let undefUnknowns ← UnifyM.findUnknownsWithUndefRanges
        match unsnoc undefUnknowns with
        | none => throwError "Unreachable case: by construction, there must exist at least one unknown with an `Undef` Range"
        | some (undefUnknownsPrefix, finalUnknown) =>
          -- For each `u ∈ undefUnknowns[0..=n-2]`, we generate `u` freely by producing the expr `let u ← arbitrary`
          for u in undefUnknownsPrefix do
            let letBindExpr ← mkLetBind (mkIdent u) #[arbitraryFn]
            doElems := doElems.push letBindExpr

          -- For the `finalUnknown`, we generate it by using the expression returned by `emitFinalCall`
          doElems := doElems.push (← emitFinalCall finalUnknown)

          -- We then update all `u ∈ undefUnknowns` to have a fixed range in `constraints`,
          -- and handle the remaining hypotheses via a recursive call to `emitHypotheses` with the updated `constraints`
          UnifyM.fixRanges undefUnknowns
          let recursiveCallResult ← UnifyM.withConstraints (fun k => emitHypotheses remainingHyps k)
          doElems := doElems.push (← `(doElem| $recursiveCallResult:term))

          -- We then put everything together in one big monadic do-block
          mkDoBlock doElems

  /-- Assembles the body of the generator (this function is called when all hypotheses have been processed by `emitHypotheses`)

      (Note that this function doesn't take in an explicit `constraints` argument (unlike the pseudocode in the paper),
      since we fetch the `constraints` map via a `get` call in the State monad) -/
  partial def finalAssembly : UnifyM (TSyntax `term) := do
    -- Find all unknowns whose ranges are `Undef`
    let undefUnknowns ← UnifyM.findUnknownsWithUndefRanges

    -- Update the constraint map so that all unknowns in `undefKnowns` now have a `Fixed` `Range`
    UnifyM.fixRanges undefUnknowns

    -- Construct the final expression that will be produced by the generator
    let unifyState ← get
    let outputName := unifyState.outputName
    let updatedConstraints := unifyState.constraints
    let result ← emitResult updatedConstraints outputName (← UnifyM.findCorrespondingRange updatedConstraints outputName)

    -- Bind each unknown in `undefUnknowns` to the result of an arbitrary call,
    -- then return the value computed in `result`
    let mut doElems := #[]
    for u in undefUnknowns do
      doElems := doElems.push (← mkLetBind (mkIdent u) #[arbitraryFn])
    doElems := doElems.push (← `(doElem| return $result))

    -- Put everything together in one monadic do-block
    mkDoBlock doElems

  /-- Produces the call to the final generator call in the body of the sub-generator -/
  partial def emitFinalCall (unknown : Unknown) : UnifyM (TSyntax `doElem) := do
    let unifyState ← get
    let outputName := unifyState.outputName
    let lhs := mkIdent unknown
    if unknown == outputName then
      -- Produce a call to `aux_arb` (recursively generate a value for the unknown)
      -- TODO: handle other arguments that need to be supplied to `aux_arb`
      mkLetBind lhs #[auxArbFn, initSizeIdent, mkIdent `size']
    else
      -- Generate a value for the unknown via a call to `arbitraryST`, passing in the final hypothesis
      -- as an argument to `arbitraryST`
      let unknownIdent := mkIdent unknown
      match unifyState.hypotheses.getLast? with
      | none => throwError m!"encountered empty list of hypotheses in emitFinalCall, state = {unifyState}"
      | some (ctorName, ctorArgs) => do
        let ctorArgsArr := Lean.mkIdent <$> ctorArgs.toArray
        let constraint ← `((fun $unknownIdent => $(mkIdent ctorName) $ctorArgsArr*))
        let rhsTerms := #[(arbitrarySTFn : TSyntax `term), constraint]
        mkLetBind lhs rhsTerms

  /-- Produces a term corresponding to the value being generated -/
  partial def emitResult (k : UnknownMap) (u : Unknown) (range : Range) : UnifyM (TSyntax `term) := do
    logError m!"emitResult called with unknown {u}, range {range}"
    match range with
    | .Unknown u' => emitResult k u' (← UnifyM.findCorrespondingRange k u')
    | .Fixed => `($(mkIdent u))
    | .Ctor c rs => do
      logWarning m!"Entered recursive case of emitResult with range = {range}"
      let ctorIdent := mkIdent c
      let ctorArgs ← Array.mapM (fun r => emitResult k u r) rs.toArray
      `($ctorIdent $ctorArgs*)
    | .Undef ty => throwError m!"Error: unknown {u} has a range of (Undef {ty}) in {k.toList}"

end


/-- Function that handles the bulk of the generator derivation algorithm for a single constructor:
    processes the entire type of the constructor within the same `LocalContext` (the one produced by `forallTelescopeReducing`)

    Takes as argument:
    - The constructor name `ctorName`
    - The name and type of the output (value to be generated)
    - The names of inputs (arguments to the generator)
    - An array of unknowns (the arguments to the inductive relation) -/
def processCtorInContext (ctorName : Name) (outputName : Name) (outputType : Expr) (inputNames : List Name) (unknowns : Array Unknown) : UnifyM (TSyntax `term) := do
  let ctorInfo ← getConstInfoCtor ctorName
  let ctorType := ctorInfo.type

  -- Stay within the forallTelescope scope for all processing
  forallTelescopeReducing ctorType (cleanupAnnotations := true) (fun forAllVarsAndHyps conclusion => do
    logWarning m!"Processing constructor {ctorName}"
    logWarning m!"conclusion = {conclusion}"

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
      | none => none)

    logWarning m!"forAllVars = {forAllVars}"
    logWarning m!"inputNames = {inputNames}"

    -- Creates the initial `UnifyState` needed for the unification algorithm
    let initialUnifyState := mkInitialUnifyState inputNames outputName outputType forAllVars.toList
    logWarning m!"initialUnifyState = {initialUnifyState}"

    -- Update the state in `UnifyM` to be `initialUnifyState`
    set initialUnifyState

    -- Get the ranges corresponding to each of the unknowns
    let unknownRanges ← unknowns.mapM processCorrespondingRange
    let unknownArgsAndRanges := unknowns.zip unknownRanges

    logWarning m!"unknownArgsAndRanges = {unknownArgsAndRanges}"

    -- Compute the appropriate `Range` for each argument in the constructor's conclusion
    let conclusionArgs := conclusion.getAppArgs
    let conclusionRanges ← conclusionArgs.mapM convertExprToRangeInCurrentContext

    let conclusionArgsAndRanges := conclusionArgs.zip conclusionRanges

    logWarning m!"conclusion = {conclusion}"
    logWarning m!"conclusionArgsAndRanges = {conclusionArgsAndRanges}"

    -- Extract hypotheses (which correspond to pairs in `forAllVarsAndHypsWithTypes` where the first component is `none`)
    -- let hypotheses := forAllVarsAndHypsWithTypes.filterMap (fun (nameOpt, tyExpr) =>
    --   match nameOpt with
    --   | none => tyExpr
    --   | some _ => none)
    -- for hyp in hypotheses do
    --   let hypRange ← convertExprToRangeInCurrentContext hyp

    -- TODO: figure out how to handle repeated unknowns in `conclusionArgsAndRanges`
    for ((u1, r1), (u2, r2)) in conclusionArgsAndRanges.zip unknownArgsAndRanges do
      logWarning m!"Unifying ({u1} ↦ {r1}) with ({u2} ↦ {r2})"
      unify r1 r2

    let finalState ← get
    logWarning m!"finalState = {finalState}"


    emitPatterns finalState.patterns finalState.equalities.toList finalState.constraints)



/-- Takes the name of a constructor and the existing `LocalContext`,
    and returns a triple consisting of:
    1. The names & types of universally quantified variables
    2. The components of the body of the constructor's arrow type (which mentions the universally quantified variables)
    3. An updated `LocalContext` populated with all the univerally quantified variables
       (this is needed for pretty-printing purposes) -/
def getCtorArgsInContext (ctorName : Name) (localCtx : LocalContext) : MetaM (Array (Name × Expr) × Array Expr × LocalContext) := do
  let ctorInfo ← getConstInfoCtor ctorName
  let ctorType := ctorInfo.type

  let (forAllVars, ctorTypeBody) := extractForAllBinders ctorType
  logWarning m!"inside getCtorArgsInContext"
  logWarning m!"forAllVars = {forAllVars}"

  let ctorTypeComponents ← getComponentsOfArrowType ctorTypeBody

  withLCtx' localCtx do
    forallTelescopeReducing ctorType (cleanupAnnotations := true) $ fun boundVars body => do
      logWarning m!"boundVars = {boundVars}"
      logWarning m!"body = {body}"
      logWarning m!"ctorTypeComponents = {ctorTypeComponents}"
      let lctx ← getLCtx
      let exprsInContext := lctx.getFVars
      logWarning m!"exprsInContext = {exprsInContext}"
      return (forAllVars, ctorTypeComponents, lctx)

/-- Command for deriving a sub-generator for one construtctor of an inductive relation (per figure 4 of GGG) -/
syntax (name := derive_subgenerator) "#derive_subgenerator" "(" "fun" "(" ident ":" term ")" "=>" term ")" : command

@[command_elab derive_subgenerator]
def elabDeriveSubGenerator : CommandElab := fun stx => do
  match stx with
  | `(#derive_subgenerator ( fun ( $var:ident : $outputTypeSyntax:term ) => $body:term )) => do

    -- Parse the body of the lambda for an application of the inductive relation
    let (inductiveSyntax, argNames) ← parseInductiveApp body
    let inductiveName := inductiveSyntax.getId

    -- Figure out the name and type of the value we wish to generate (the "output")
    let outputName := var.getId
    let outputType ← liftTermElabM $ elabTerm outputTypeSyntax none

    -- Find the index of the argument in the inductive application for the value we wish to generate
    -- (i.e. find `i` s.t. `args[i] == targetVar`)
    let outputIdxOpt := findTargetVarIndex outputName argNames
    if let .none := outputIdxOpt then
      throwError "cannot find index of value to be generated"
    let outputIdx := Option.get! outputIdxOpt

    -- Each argument to the inductive relation (except the one at `outputIdx`)
    -- is treated as an input
    let inputNames := TSyntax.getId <$> Array.eraseIdx! argNames outputIdx

    -- Each argument to the inductive relation (as specified by the user) is treated as an unknown
    -- (including the output variable)
    let allUnknowns := TSyntax.getId <$> argNames

    -- Obtain Lean's `InductiveVal` data structure, which contains metadata about the inductive relation
    let inductiveVal ← getConstInfoInduct inductiveName

    for ctorName in inductiveVal.ctors do
      -- Process everything within the scope of the telescope
      let derivationResult ← liftTermElabM $ UnifyM.runInMetaM
        (processCtorInContext ctorName outputName outputType inputNames.toList allUnknowns) emptyUnifyState
      match derivationResult with
      | some (generator, _) => logInfo m!"Derived generator:\n```\n{generator}\n```"
      | none => logInfo m!"Derived generator:\n```\nreturn none\n```"



  | _ => throwUnsupportedSyntax


set_option maxRecDepth 50000

-- Example usage:
#derive_subgenerator (fun (e : term) => typingAlt Γ e τ)
