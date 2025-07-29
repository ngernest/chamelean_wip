
import Plausible.IR.Examples
import Plausible.New.GenProofTactics
import Plausible.New.OptionTGenTheorems
open Plausible
open OptionTGen


def genBalancedTree (n : Nat) : Nat → OptionT Gen Tree :=
  let rec aux_arb (initSize : Nat) (size : Nat) (n_0 : Nat) : OptionT Gen Tree :=
      match size with
      | .zero =>
        backtrack [
          (1, thunkGen $ fun _ =>
              match n_0 with
              | .zero => pure .Leaf
              | .succ _ => OptionT.fail),
          (1, thunkGen $ fun _ =>
              match n_0 with
              | 1 => pure .Leaf
              | _ => OptionT.fail),
          (1, thunkGen $ fun _ => OptionT.fail)
        ]
      | .succ size' =>
        backtrack [
          (1, thunkGen $ fun _ =>
              match n_0 with
              | .zero => pure .Leaf
              | _ => OptionT.fail),
          (1, thunkGen $ fun _ =>
              match n_0 with
              | 1 => pure .Leaf
              | _ => OptionT.fail),
          (.succ size', thunkGen $ fun _ =>
            match n_0 with
            | .zero => OptionT.fail
            | .succ n => do
              let l ← aux_arb initSize size' n
              let r ← aux_arb initSize size' n
              let x ← SampleableExt.interpSample Nat
              pure (.Node x l r))
        ]
  termination_by size
  fun size => aux_arb size size n


theorem genBalancedTree_correct: OptionTGenEnsure (balanced n) (genBalancedTree n size) := by
  gen_proof
