import Plausible.IR.Examples

import Plausible.Gen
import Plausible.Sampleable
open Plausible

namespace OptionTGen

--------------------------------------------------------------------------
-- Helper functions (adapted from QuickChick sourcecode)
-- https://github.com/QuickChick/QuickChick/blob/master/src/Generators.v
--------------------------------------------------------------------------

/-- `pickDrop xs n` returns a weight & its generator `(k, gen)` such that `n < k`,
    and also returns the tail of the list after `(k, gen)` -/
def pickDrop (xs : List (Nat × OptionT Gen α)) (n : Nat) : Nat × OptionT Gen α × List (Nat × OptionT Gen α) :=
  match xs with
  | [] => (0, OptionT.fail, [])
  | (k, x) :: xs =>
    if n < k then (k, x, xs)
    else
      let (k', x', xs') := pickDrop xs (n - k)
      (k', x', (k, x)::xs')

/-- Sums all the weights in an association list containing `Nat`s and `α`s -/
def sumFst (gs : List (Nat × α)) : Nat :=
  List.foldl (fun acc p => acc + p.fst) 0 gs

/-- Helper function for `backtrack` which picks one out of `total` generators with some initial amount of `fuel` -/
def backtrackFuel (fuel : Nat) (total : Nat) (gs : List (Nat × OptionT Gen α)) : OptionT Gen α :=
  match fuel with
  | .zero => OptionT.fail
  | .succ fuel' => do
    let n ← Gen.choose Nat 0 (total - 1) (by omega)
    let (k, g, gs') := pickDrop gs n
    -- Try to generate a value using `g`, if it fails, backtrack with `fuel'`
    -- and pick one out of the `total - k` remaining generators
    OptionT.tryCatch g (fun () => backtrackFuel fuel' (total - k) gs')

/-- Tries all generators until one returns a Some value or all failed once with None.
   The generators are picked at random according to their weights (like frequency), and each one is run at most once. -/
def backtrack (gs : List (Nat × OptionT Gen α)) : OptionT Gen α :=
  backtrackFuel (gs.length) (sumFst gs) gs

/-- Delays the evaluation of a generator by taking in a function `f : Unit → OptionT Gen α` -/
def thunkGen (f : Unit → OptionT Gen α) : OptionT Gen α :=
  f ()

/-- Samples from an `OptionT Gen` generator that is parameterized by its `size`,
    returning the generated `Option α`  in the `IO` monad -/
def runSizedGen {α} (sizedGen : Nat → OptionT Gen α) (size : Nat) : IO (Option α) :=
  Gen.run (OptionT.run $ sizedGen size) size

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

-- Example usage:
-- To sample from the generator, we have to do `OptionT.run` to extract the underlying generator,
-- then invoke `Gen.run` to display the generated value in the IO monad
-- def tempSize := 5
-- #eval runSizedGen (genBST 1 10) tempSize
-- #eval runSizedGen (genBalancedTree 2) tempSize

end OptionTGen
