import Lean
import Std
import Batteries

import Plausible.GeneratingGoodGenerators.UnificationMonad
import Plausible.New.DeriveConstrainedProducers
import Plausible.New.SubGenerators
import Plausible.New.DeriveArbitrary
import Plausible.New.Debug
import Plausible.IR.Examples


open Lean Elab Command Meta Term Parser
open Idents

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

/-- Command for deriving a sub-generator for one construtctor of an inductive relation (per figure 4 of GGG) -/
syntax (name := derive_subgenerator) "#derive_subgenerator" "(" "fun" "(" ident ":" term ")" "=>" term ")" : command


@[command_elab derive_subgenerator]
def elabDeriveSubGenerator : CommandElab := fun stx => do
  match stx with
  | `(#derive_subgenerator ( fun ( $var:ident : $outputTypeSyntax:term ) => $body:term )) => do

    -- Parse the body of the lambda for an application of the inductive relation
    let (inductiveName, args) ← parseInductiveApp body

    let outputName := var.getId
    let outputType ← liftTermElabM $ elabTerm outputTypeSyntax none

    -- Find the index of the argument in the inductive application for the value we wish to generate
    -- (i.e. find `i` s.t. `args[i] == targetVar`)
    let outputIdxOpt := findTargetVarIndex outputName args
    if let .none := outputIdxOpt then
      throwError "cannot find index of value to be generated"
    let outputIdx := Option.get! outputIdxOpt

    let inputNames := TSyntax.getId <$> Array.eraseIdx! args outputIdx

    -- Obtain Lean's `InductiveVal` data structure, which contains metadata about the inductive relation
    let inductiveVal ← getConstInfoInduct inductiveName
    for ctorName in inductiveVal.ctors do
      -- Get all the names & types of the constructor's arguments
      let ctorArgNamesTypes ← liftTermElabM $ getCtorArgsNamesAndTypes ctorName

      logInfo m!"ctor = {ctorName}"

      let mut forAllVariables := #[]
      for (arg, argTy) in ctorArgNamesTypes do
        let isProp ← liftTermElabM $ Meta.isProp argTy

        -- If `argTy` is *not* a `Prop`, then we know `arg` is a universally quantified variable,
        -- which we treat as an `Unknown` that maps to an `Undef` `Range`
        if !isProp then
          forAllVariables := forAllVariables.push (arg, argTy)

      let initialUnifyState := mkInitialUnifyState inputNames.toList outputName outputType forAllVariables.toList

      -- let conclusion := ctorArgNamesTypes.back!
      logInfo m!"ctorArgNamesTypes = {ctorArgNamesTypes}"

      -- TODO: implement rest of algorithm

  | _ => throwUnsupportedSyntax


-- Example usage:
-- #derive_subgenerator (fun (t : Tree) => complete n t)


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
