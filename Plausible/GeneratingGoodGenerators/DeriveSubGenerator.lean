import Lean
import Std
import Batteries

import Plausible.GeneratingGoodGenerators.UnificationMonad
import Plausible.New.DeriveConstrainedProducers
import Plausible.New.SubGenerators
import Plausible.New.DeriveArbitrary
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
def mkInitialConstraintMap (inputNames: List Name) (outputName : Name) (outputType : Expr) (forAllVariables : List (Name × Expr)): ConstraintMap :=
  let inputConstraints := inputNames.zip (List.replicate inputNames.length .Fixed)
  let outputConstraints := [(outputName, .Undef outputType)]
  let forAllVarsConstraints := (fun (x, ty) => (x, .Undef ty)) <$> forAllVariables
  Std.HashMap.ofList $ inputConstraints ++ outputConstraints ++ forAllVarsConstraints

/-- Creates the initial `UnifyState` where the constraint map is created using `mkInitialConstraintMap` -/
def mkInitialUnifyState (inputNames : List Name) (outputName : Name) (outputType : Expr) (forAllVariables : List (Name × Expr)) : UnifyState :=
  let forAllVarNames := Prod.fst <$> forAllVariables
  let constraints := mkInitialConstraintMap inputNames outputName outputType forAllVariables
  let unknowns := Std.HashSet.ofList (outputName :: (inputNames ++ forAllVarNames))
  {
    constraints := constraints
    equalities := ∅
    patterns := []
    unknowns := unknowns
  }

/-- Converts a expression `e` to a *constructor expression* `C r1 … rn`,
    where `C` is a constructor and the `ri` are arguments,
    returning `some (C, #[r1, …, rn])`
    - If `e` is not an application, this function returns `none`  -/
def convertToCtorExpr (e : Expr) : Option (Name × Array Expr) :=
  if !e.isApp then none
  else some e.getAppFnArgs

/-- Converts an `Expr` to a `Range`, using the `LocalContext` to find the user-facing names
    corresponding to `FVarId`s -/
partial def convertExprToRange (e : Expr) (localCtx : LocalContext) : MetaM Range :=
  match convertToCtorExpr e with
  | some (f, args) => do
    let argRanges ← List.mapM (fun arg => convertExprToRange arg localCtx) args.toList
    return (Range.Ctor f argRanges)
  | none =>
    -- `e` is an identifier (a `FVarId`)
    withLCtx' localCtx do
      if localCtx.containsFVar e then
        logInfo m!"{repr e} is in LocalContext"
      else
        logInfo m!"{repr e} not in LocalContext"
      match localCtx.find? e.fvarId! with
      | some localDecl => return (Range.Unknown localDecl.userName)
      | none =>
        let name := getUserNameInContext! localCtx e.fvarId!
        let namesInContext := (fun e => getUserNameInContext! localCtx e.fvarId!) <$> localCtx.getFVars
        if namesInContext.contains name then
          return (Range.Unknown name)
        else
          -- TODO: figure out why `lo` isn't in the `LocalContext` for the BST example
          throwError m!"{e} missing from LocalContext, which only contains {namesInContext}"


-- The following implements the `emit` functions in Figure 4
-- TODO: fill in the metaprogramming stuff

mutual

  /-- Produces the code for a pattern match on an unknown -/
  partial def emitPatterns (patterns : List (Unknown × Pattern)) (equalities : List (Unknown × Unknown)) (constraints : ConstraintMap) : MetaM (TSyntax `term) :=
    match patterns with
    | [] => emitEqualities equalities constraints
    | (u, p) :: ps => sorry

  /-- Produces the code for an equality check -/
  partial def emitEqualities (equalities : List (Unknown × Unknown)) (constraints : ConstraintMap) : MetaM (TSyntax `term) :=
    match equalities with
    | [] => sorry -- figure out how to get `S e`
    | (u1, u2) :: eqs => sorry

  /-- Produces the code for the body of a sub-generator which processes hypotheses -/
  partial def emitHypothesis (hypotheses : List (Name × List Unknown)) (constraints : ConstraintMap) : MetaM (TSyntax `term) :=
    match hypotheses with
    | [] => finalAssembly constraints
    | _ => sorry

  /-- Assembles the body of the generator (this function is called when all hypotheses have ben processed by `emitHypotheses`) -/
  partial def finalAssembly (constraints : ConstriantMap) : MetaM (TSyntax `term) :=
    sorry

  /-- Produces the call to the final generator call in the body of the sub-generator -/
  partial def emitFinalCall (unknown : Unknown) : MetaM (TSyntax `doElem) := sorry

  /-- Produces a term corresponding to the value being generated -/
  partial def emitResult (k : ConstraintMap) (u : Unknown) (range : Range) : MetaM (TSyntax `term) :=
    match range with
    | .Unknown u' => emitResult k u' k[u']!
    | .Fixed => `($(mkIdent u))
    | .Ctor c rs => do
      let rs' ← List.mapM (fun r => emitResult k u r) rs
      sorry
    | .Undef ty => throwError s!"encountered Range of (Undef {ty}) in emitResult"

end

-- This function is only for handling freshening top-level args to the generator (ignored for now)
-- def addInputsToLocalContext (inputExpr : Expr) (argNames : Array Name) := do
--   match inputExpr.getAppFn.constName? with
--   | some inductiveName => do
--     let type ← inferType inputExpr
--     let arrowTypeComponents ← getComponentsOfArrowType type

--     -- `input_types` contains all elements of `tyexprs_in_arrow_type` except the conclusion (which is `Prop`)
--     let inputTypes := arrowTypeComponents.pop

--     let (inputVars, inputVarNames, localCtx, nameMap) ← mkInitialContextForInductiveRelation inputTypes argNames

--     withLCtx' localCtx do
--       -- inputVars contains the original names of the args to the inductive relation
--       logInfo m!"inputVars = {inputVars}"

--       -- inputVarNames contains the freshened names
--       logInfo m!"inputVarNames = {inputVarNames}"

--       -- TODO: remove dummy return expr
--       return (localCtx, nameMap)
--   | none => throwError "input expression is not a function application"


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

    let inputNames := TSyntax.getId <$> Array.eraseIdx! argNames outputIdx

    let mut localCtx ← liftTermElabM getLCtx

    -- Obtain Lean's `InductiveVal` data structure, which contains metadata about the inductive relation
    let inductiveVal ← getConstInfoInduct inductiveName
    for ctorName in inductiveVal.ctors do
      logInfo m!"ctorName = {ctorName}"

      let (forAllVars, ctorTypeComponents, updatedCtx) ← liftTermElabM $ getCtorArgsInContext ctorName localCtx
      localCtx := updatedCtx

      if ctorTypeComponents.isEmpty then
        throwError "constructor {ctorName} has a malformed type expression"

      let initialUnifyState := mkInitialUnifyState inputNames.toList outputName outputType forAllVars.toList
      logInfo m!"{initialUnifyState}"

      -- Convert each arugment in the constructor's conclusion to a range
      let conclusion := ctorTypeComponents.back!
      let conclusionArgs := conclusion.getAppArgs
      let conclusionArgRanges ← Array.mapM (fun e => liftTermElabM $ convertExprToRange e localCtx) conclusionArgs

      logInfo m!"conclusionArgs = {conclusionArgs}"
      logInfo m!"conclusionArgRanges = {conclusionArgRanges}"



      -- TODO: implement rest of algorithm


  | _ => throwUnsupportedSyntax


-- Example usage:
#derive_subgenerator (fun (tree : Tree) => bst lo hi tree)


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
