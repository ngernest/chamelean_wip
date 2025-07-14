import Lean
import Std
import Batteries

import Plausible.GeneratingGoodGenerators.UnificationMonad
import Plausible.New.DeriveConstrainedProducers
import Plausible.New.SubGenerators
import Plausible.New.DeriveArbitrary
import Plausible.New.TSyntaxCombinators
import Plausible.New.Debug
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
  { constraints := constraints
    equalities := ∅
    patterns := []
    unknowns := unknowns }

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

    However, there are 3 conditions in which we generate a fresh unknown `u'`,
    register the equality `u' = u` and update the `constraints` map
    with the binding `u' |-> Unknown u`:

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
      UnifyM.registerEquality u' u
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
  partial def emitPatterns (patterns : List (Unknown × Pattern)) (equalities : List (Unknown × Unknown)) (constraints : UnknownMap) : MetaM (TSyntax `term) :=
    match patterns with
    | [] => emitEqualities equalities constraints
    | (u, p) :: ps => do
      let caseRHS ← emitPatterns ps equalities constraints
      let caseLHS ← convertPatternToTerm p
      let case ← `(Term.matchAltExpr| | $caseLHS => $caseRHS)
      let cases : TSyntaxArray ``Parser.Term.matchAlt := #[]
      mkMatchExpr (mkIdent u) cases

  /-- Produces the code for an equality check -/
  partial def emitEqualities (equalities : List (Unknown × Unknown)) (constraints : UnknownMap) : MetaM (TSyntax `term) :=
    match equalities with
    | [] => sorry -- figure out how to get `S e`
    | (u1, u2) :: eqs => do
      let trueBranch ← emitEqualities eqs constraints
      `(if ($(mkIdent u1) == $(mkIdent u2)) then $trueBranch else $failFn)

  /-- Produces the code for the body of a sub-generator which processes hypotheses -/
  partial def emitHypothesis (hypotheses : List (Name × List Unknown)) (constraints : UnknownMap) : MetaM (TSyntax `term) :=
    match hypotheses with
    | [] => finalAssembly constraints
    | _ => sorry

  /-- Assembles the body of the generator (this function is called when all hypotheses have ben processed by `emitHypotheses`) -/
  partial def finalAssembly (constraints : ConstriantMap) : MetaM (TSyntax `term) :=
    sorry

  /-- Produces the call to the final generator call in the body of the sub-generator -/
  partial def emitFinalCall (unknown : Unknown) : MetaM (TSyntax `doElem) := sorry

  /-- Produces a term corresponding to the value being generated -/
  partial def emitResult (k : UnknownMap) (u : Unknown) (range : Range) : MetaM (TSyntax `term) :=
    match range with
    | .Unknown u' => emitResult k u' k[u']!
    | .Fixed => `($(mkIdent u))
    | .Ctor c rs => do
      let rs' ← List.mapM (fun r => emitResult k u r) rs
      sorry
    | .Undef ty => throwError m!"encountered Range of (Undef {ty}) in emitResult"

end


/-- Function that handles the bulk of the generator derivation algorithm for a single constructor:
    processes the entire type of the constructor within the same `LocalContext` (the one produced by `forallTelescopeReducing`)

    Takes as argument:
    - The constructor name `ctorName`
    - The name and type of the output (value to be generated)
    - The names of inputs (arguments to the generator)
    - An array of unknowns (the arguments to the inductive relation) -/
def processCtorInContext (ctorName : Name) (outputName : Name) (outputType : Expr) (inputNames : List Name) (unknowns : Array Unknown) : UnifyM Unit := do
  let ctorInfo ← getConstInfoCtor ctorName
  let ctorType := ctorInfo.type

  -- Stay within the forallTelescope scope for all processing
  forallTelescopeReducing ctorType (cleanupAnnotations := true) (fun forAllVarsAndHyps conclusion => do
    logInfo m!"Processing constructor {ctorName}"
    logInfo m!"conclusion = {conclusion}"

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

    logInfo m!"forAllVars = {forAllVars}"
    logInfo m!"inputNames = {inputNames}"

    -- Creates the initial `UnifyState` needed for the unification algorithm
    let initialUnifyState := mkInitialUnifyState inputNames outputName outputType forAllVars.toList
    logInfo m!"initialUnifyState = {initialUnifyState}"

    -- Update the state in `UnifyM` to be `initialUnifyState`
    set initialUnifyState

    -- Get the ranges corresponding to each of the unknowns
    let unknownRanges ← unknowns.mapM processCorrespondingRange
    let unknownArgsAndRanges := unknowns.zip unknownRanges

    logInfo m!"unknownArgsAndRanges = {unknownArgsAndRanges}"

    -- Now convert expressions while staying in the same context
    let conclusionArgs := conclusion.getAppArgs
    let conclusionRanges ← conclusionArgs.mapM convertExprToRangeInCurrentContext

    let conclusionArgsAndRanges := conclusionArgs.zip conclusionRanges

    logInfo m!"conclusion = {conclusion}"
    logInfo m!"conclusionArgsAndRanges = {conclusionArgsAndRanges}"

    -- Extract hypotheses (which correspond to pairs in `forAllVarsAndHypsWithTypes` where the first component is `none`)
    -- let hypotheses := forAllVarsAndHypsWithTypes.filterMap (fun (nameOpt, tyExpr) =>
    --   match nameOpt with
    --   | none => tyExpr
    --   | some _ => none)
    -- for hyp in hypotheses do
    --   let hypRange ← convertExprToRangeInCurrentContext hyp


    for ((u1, r1), (u2, r2)) in conclusionArgsAndRanges.zip unknownArgsAndRanges do
      logInfo m!"Unifying ({u1} ↦ {r1}) with ({u2} ↦ {r2})"
      unify r1 r2

    let finalState ← get
    logInfo m!"finalState = {finalState}")



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
  logInfo m!"inside getCtorArgsInContext"
  logInfo m!"forAllVars = {forAllVars}"

  let ctorTypeComponents ← getComponentsOfArrowType ctorTypeBody

  withLCtx' localCtx do
    forallTelescopeReducing ctorType (cleanupAnnotations := true) $ fun boundVars body => do
      logInfo m!"boundVars = {boundVars}"
      logInfo m!"body = {body}"
      logInfo m!"ctorTypeComponents = {ctorTypeComponents}"
      let lctx ← getLCtx
      let exprsInContext := lctx.getFVars
      logInfo m!"exprsInContext = {exprsInContext}"
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
      let _ ← liftTermElabM (UnifyM.runInMetaM (processCtorInContext ctorName outputName outputType inputNames.toList allUnknowns) emptyUnifyState)



  | _ => throwUnsupportedSyntax


-- Example usage:
#derive_subgenerator (fun (e : term) => typing Γ e τ)
-- #derive_subgenerator (fun (tree : Tree) => goodTree in1 in2 tree)


/-- Example initial constraint map from Section 4.2 of GGG -/
def bstInitialConstraints := Std.HashMap.ofList [
  (`hi, .Undef (mkConst `Nat)),
  (`tree, .Undef (mkConst `Tree)),
  (`in2, .Fixed),
  (`l, .Undef (mkConst `Tree)),
  (`x, .Undef (mkConst `Nat)),
  (`lo, .Undef (mkConst `Nat)),
  (`r, .Undef (mkConst `Tree)),
  (`in1, Range.Fixed)
]
