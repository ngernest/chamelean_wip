import Plausible.IR.Examples
import Plausible.New.OptionTGen
import Plausible.New.GenSuchThat

import Plausible.Gen
open Plausible
open OptionTGen

open GenSizedSuchThat

--------------------------------------------------------------------------
-- Some example `OptionT Gen α` generators
--------------------------------------------------------------------------

/-- A handwritten generator for BSTs (modelled after the automatically derived generator produced by QuickChick).
    Note that:
   - We use the `OptionT` monad to add the possibility of failure to the `Gen` monad
   - All the generators supplied to the `backtrack` combinator are thunked, to avoid unnecessary
     computation (since Lean is strict) -/
def genBST (lo : Nat) (hi : Nat) : Nat → OptionT Gen Tree :=
  let rec aux_arb (size : Nat) (lo : Nat) (hi : Nat) : OptionT Gen Tree :=
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
          if (lo < x && x < hi) then
            let l ← aux_arb size' lo x
            let r ← aux_arb size' x hi
            pure (.Node x l r)
          else OptionT.fail)
      ]
  fun size => aux_arb size lo hi

instance : GenSizedSuchThat Tree (fun t => bst lo hi t) where
  genSizedST := genBST lo hi

/-- A handwritten generator for balanced trees of height `n`
    (modelled after the automatically derived generator produced by QuickChick) -/
def genBalancedTree (n : Nat) : Nat → OptionT Gen Tree :=
  let rec aux_arb (size : Nat) (n : Nat) : OptionT Gen Tree :=
    match size with
    | .zero =>
      backtrack [
        (1, thunkGen $ fun _ =>
            match n with
            | .zero => pure .Leaf
            | .succ _ => OptionT.fail),
        (1, thunkGen $ fun _ =>
            match n with
            | 1 => pure .Leaf
            | _ => OptionT.fail),
        (1, thunkGen $ fun _ => OptionT.fail)
      ]
    | .succ size' =>
      backtrack [
        (1, thunkGen $ fun _ =>
            match n with
            | .zero => pure .Leaf
            | _ => OptionT.fail),
        (1, thunkGen $ fun _ =>
            match n with
            | 1 => pure .Leaf
            | _ => OptionT.fail),
        (.succ size', thunkGen $ fun _ =>
          match n with
          | .zero => OptionT.fail
          | .succ n => do
            let l ← aux_arb size' n
            let r ← aux_arb size' n
            let x ← SampleableExt.interpSample Nat
            pure (.Node x l r))
      ]
  fun size => aux_arb size n


instance : GenSizedSuchThat Tree (fun t => balanced n t) where
  genSizedST := genBalancedTree n

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
