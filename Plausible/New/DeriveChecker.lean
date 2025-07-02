import Lean
import Plausible.IR.Prelude
import Plausible.New.DeriveGenerator
import Plausible.New.SubCheckers

open Lean Elab Command Meta Term Parser
open Plausible.IR

----------------------------------------------------------------------
-- Command elaborator for deriving checkers
-----------------------------------------------------------------------

syntax (name := derive_checker) "#derive_checker" "(" term ")" : command

/-- Command elaborator that produces the function header for the checker -/
@[command_elab derive_checker]
def elabDeriveChecker : CommandElab := fun stx => do
  match stx with
  | `(#derive_checker ( $body:term )) => do
    -- Parse the body of the lambda for an application of the inductive relation
    let (inductiveName, args) ← deconstructInductiveApplication body

    -- Elaborate the name of the inductive relation and the type
    -- of the value to be generated
    let inductiveExpr ← liftTermElabM $ elabTerm inductiveName none

    let argNameStrings := convertIdentsToStrings args

    -- Create an auxiliary `SubGeneratorInfo` structure that
    -- stores the metadata for each derived sub-generator
    let allSubCheckerInfos ← liftTermElabM $ getSubCheckerInfos inductiveExpr argNameStrings

    -- for sc in allSubCheckerInfos do
    --   logInfo m!"subChecker = {sc}"

    -- Every generator is an inductive generator
    -- (they can all be invoked in the inductive case of the top-level generator),
    -- but only certain generators qualify as `BaseGenerator`s
    let baseCheckerInfos := Array.filter (fun checker => checker.checkerSort == .BaseChecker) allSubCheckerInfos
    let inductiveCheckerInfos := allSubCheckerInfos

    let _ ← Array.mapM (fun chk => liftTermElabM $ mkSubChecker chk) baseCheckerInfos
    let _ ← Array.mapM (fun chk => liftTermElabM $ mkSubChecker chk) inductiveCheckerInfos

  | _ => throwUnsupportedSyntax

-- TODO: see if we can implement a deriving handler to support
-- `deriving instance DecOpt for (bst lo hi t)` syntax

-- #derive_checker (bst lo hi t)
-- #derive_checker (balanced n t)
-- #derive_checker (lookup Γ x τ)
-- #derive_checker (typing Γ e τ)

/-

let rec aux_arb (init_size : Nat) (size : Nat) (lo_0 : Nat) (hi_0 : Nat) (t_0 : Tree) : Option Bool :=
  match size with
  | .zero =>
    DecOpt.checkerBacktrack [
      fun _ =>
        match t_0 with
        | .Leaf => some true
        | .Node _ _ _ => some false,
      fun _ => none
    ]
  | .succ size' =>
    DecOpt.checkerBacktrack [
      fun _ =>
        match t_0 with
        | .Leaf => some true
        | .Node _ _ _ => some false,
      fun _ =>
        match t_0 with
        | .Leaf => some false
        | .Node x l r =>
          DecOpt.andOptList [
            DecOpt.decOpt (lo_0 < x && x < hi_0) init_size,
            aux_arb init_size size' lo_0 x l,
            aux_arb init_size size' x hi_0 r
          ]
    ]

-/
