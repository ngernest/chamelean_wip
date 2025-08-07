import Plausible.IR.Examples
import Plausible.New.OptionTGen
import Plausible.New.Arbitrary
import Plausible.New.ArbitrarySizedSuchThat
import Plausible.New.DecOpt

import Plausible.Gen
open Plausible
open OptionTGen

open ArbitrarySizedSuchThat

set_option linter.missingDocs false

--------------------------------------------------------------------------
-- Some example `OptionT Gen α` generators
--------------------------------------------------------------------------

/-- `arbitrarySizedST` contains a handwritten generator for BSTs
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
          let x ← Arbitrary.arbitrary
          if (lo_0 < x && x < hi_0) then
            let l ← aux_arb initSize size' lo_0 x
            let r ← aux_arb initSize size' x hi_0
            pure (.Node x l r)
          else OptionT.fail)
      ]
  fun size => aux_arb size size lo hi

/- Instance of the `ArbitrarySizedSuchThat` typeclass for generators of BSTs -/
-- instance : ArbitrarySizedSuchThat Tree (fun t => bst lo hi t) where
--   arbitrarySizedST := genBST lo hi

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
              let x ← Arbitrary.arbitrary
              pure (.Node x l r))
        ]
  fun size => aux_arb size size n

/- Instance of the `ArbitrarySizedSuchThat` typeclass for generators of balanced trees
   of height `n` -/
-- instance : ArbitrarySizedSuchThat Tree (fun t => balanced n t) where
--   arbitrarySizedST := genBalancedTree n


/-
Example usage:

To sample from the derived generator, we apply the `arbitrarySizedST` function
(from the `ArbitrarySizedSuchThat` typeclass) onto the proposition that constrains
the generated values (e.g. `fun t => balanced 5 t` for balanced trees of height 5).
We then invoke `runSizedGen` to display the generated value in the `IO` monad.

For example:
```
def tempSize := 10
#eval runSizedGen (arbitrarySizedST (fun t => balanced 5 t)) tempSize
```
-/


/-- Handwritten `DecOpt` instance for the proposition `bst lo hi t` -/
instance : DecOpt (bst lo hi t) where
  decOpt :=
    let rec aux_arb (initSize : Nat) (size : Nat) (lo_0 : Nat) (hi_0 : Nat) (t_0 : Tree) : Option Bool :=
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
                DecOpt.decOpt (lo_0 < x && x < hi_0) initSize,
                aux_arb initSize size' lo_0 x l,
                aux_arb initSize size' x hi_0 r
              ]
        ]
    fun size => aux_arb size size lo hi t

/-- Handwritten `DecOpt` instance for the proposition `balanced n t` -/
instance : DecOpt (balanced n t) where
  decOpt :=
    let rec aux_arb (initSize : Nat) (size : Nat) (n_0 : Nat) (t_0 : Tree) : Option Bool :=
      match size with
      | .zero =>
        DecOpt.checkerBacktrack [
          (fun _ =>
            match t_0 with
            | .Leaf => match n_0 with
                      | 0 => some true
                      | _ => some false
            | _ => some false),
          (fun _ =>
            match t_0 with
            | .Leaf => match n_0 with
                      | 1 => some true
                      | _ => some false
            | _ => some false),
          (fun _ => none)
        ]
      | .succ size' =>
        DecOpt.checkerBacktrack [
          (fun _ =>
            match t_0 with
            | .Leaf => match n_0 with
                      | 0 => some true
                      | _ => some false
            | _ => some false),
          (fun _ =>
            match t_0 with
            | .Leaf => match n_0 with
                      | 1 => some true
                      | _ => some false
            | _ => some false),
          (fun _ =>
            match t_0 with
            | .Leaf => some false
            | .Node _ l r =>
              match n_0 with
              | .succ n =>
                DecOpt.andOptList [
                  aux_arb initSize size' n l,
                  aux_arb initSize size' n r
                ]
              | _ => some false)
        ]
    fun size => aux_arb size size n t
