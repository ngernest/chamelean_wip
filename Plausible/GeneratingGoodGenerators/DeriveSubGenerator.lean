import Lean
import Std

import Plausible.GeneratingGoodGenerators.UnificationMonad
import Plausible.New.DeriveConstrainedProducers
import Plausible.New.SubGenerators
import Plausible.New.DeriveArbitrary
import Plausible.IR.Examples

open Lean Elab Command Meta Term Parser
open Idents

---------------------------------------------------------------------------------------------
-- Implements figure 4 from "Generating Good Generators for Inductive Relations", POPL '18
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
  partial def emitPatterns (patterns : List (Unknown × Pattern)) (equalities : List (Unknown × Unknown)) (constraints : ConstraintMap) : MetaM (TSyntax `term) :=
    match patterns with
    | [] => emitEqualities equalities constraints
    | (u, p) :: ps => sorry

  partial def emitEqualities (equalities : List (Unknown × Unknown)) (constraints : ConstraintMap) : MetaM (TSyntax `term) :=
    match equalities with
    | [] => sorry -- figure out how to get `S e`
    | (u1, u2) :: eqs => sorry

  partial def emitHypothesis (hypotheses : List (Name × List Unknown)) (constraints : ConstraintMap) : MetaM (TSyntax `term) :=
    match hypotheses with
    | [] => finalAssembly constraints
    | _ => sorry

  partial def finalAssembly (constraints : ConstriantMap) : MetaM (TSyntax `term) :=
    sorry

  partial def emitFinalCall (unknown : Unknown) : MetaM (TSyntax `doElem) := sorry

  partial def emitResult (k : ConstraintMap) (u : Unknown) (range : Range) : MetaM (TSyntax `term) :=
    match range with
    | .Unknown u' => emitResult k u' k[u']!
    | .Fixed => `($(mkIdent u))
    | .Ctor c rs => do
      let rs' ← List.mapM (fun r => emitResult k u r) rs
      sorry
    | .Undef ty => throwError s!"encountered Range of (Undef {ty}) in emitResult"
end

-- Command elaborator infrastructure below

syntax (name := derive_subgenerator) "#derive_subgenerator" "(" "fun" "(" ident ":" term ")" "=>" term ")" : command

@[command_elab derive_subgenerator]
def elabDeriveSubGenerator : CommandElab := fun stx => do
  match stx with
  | `(#derive_subgenerator ( fun ( $var:ident : $targetTypeSyntax:term ) => $body:term )) => do

    -- Parse the body of the lambda for an application of the inductive relation
    let (inductiveName, args) ← parseInductiveApp body
    let targetVar := var.getId


    -- Find the index of the argument in the inductive application for the value we wish to generate
    -- (i.e. find `i` s.t. `args[i] == targetVar`)
    let targetIdxOpt := findTargetVarIndex targetVar args
    if let .none := targetIdxOpt then
      throwError "cannot find index of value to be generated"
    let targetIdx := Option.get! targetIdxOpt

    -- Obtain Lean's `InductiveVal` data structure, which contains metadata about the inductive relation
    let inductiveVal ← getConstInfoInduct inductiveName

    logInfo m!"ctors = {inductiveVal.ctors}"


  | _ => throwUnsupportedSyntax


-- Example usage:
-- #derive_subgenerator (fun (t : Tree) => bst lo hi t)
