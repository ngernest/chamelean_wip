import Plausible.IR.Examples
import Plausible.New.OptionTGen
import Plausible.New.GenSizedSuchThat

import Plausible.Gen
open Plausible
open OptionTGen

open GenSizedSuchThat

--------------------------------------------------------------------------
-- Some example `OptionT Gen α` generators
--------------------------------------------------------------------------

/- `genSizedST` contains a handwritten generator for BSTs
    (modelled after the automatically derived generator produced by QuickChick).
    Note that:
    - We use the `OptionT` monad transformer to add the possibility of failure to the `Gen` monad
    - All the generators supplied to the `backtrack` combinator are thunked, to avoid unnecessary
      computation (since Lean is strict) -/
def genBST (lo : Nat) (hi : Nat) : Nat → OptionT Gen Tree :=
  let rec aux_arb (initSize : Nat) (size : Nat) (lo_0 : Nat) (hi_0 : Nat) : OptionT Gen Tree :=
    match size with
    | .zero =>
      backtrack [
        (1, thunkGen $ fun _ => pure .Leaf),
        (1, thunkGen $ fun _ => OptionT.fail)
      ]
    | .succ size' =>
      backtrack [
        (1, thunkGen $ fun _ => pure .Leaf),
        (.succ size', thunkGen $ fun _ => do
          let x ← SampleableExt.interpSample Nat
          if (lo_0 < x && x < hi_0) then
            let l ← aux_arb initSize size' lo_0 x
            let r ← aux_arb initSize size' x hi_0
            pure (.Node x l r)
          else OptionT.fail)
      ]
  fun size => aux_arb size size lo hi

/- Instance of the `GenSizedSuchThat` typeclass for generators of BSTs -/
-- instance : GenSizedSuchThat Tree (fun t => bst lo hi t) where
--   genSizedST := genBST lo hi

/-- A handwritten generator for balanced trees of height `n`
    (modelled after the automatically derived generator produced by QuickChick) -/
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
  fun size => aux_arb size size n

/- Instance of the `GenSizedSuchThat` typeclass for generators of balanced trees
   of height `n` -/
-- instance : GenSizedSuchThat Tree (fun t => balanced n t) where
--   genSizedST := genBalancedTree n


/-
Example usage:

To sample from the derived generator, we apply the `genSizedST` function
(from the `GenSizedSuchThat` typeclass) onto the proposition that constrains
the generated values (e.g. `fun t => balanced 5 t` for balanced trees of height 5).
We then invoke `runSizedGen` to display the generated value in the `IO` monad.

For example:
```
def tempSize := 10
#eval runSizedGen (genSizedST (fun t => balanced 5 t)) tempSize
```
-/
