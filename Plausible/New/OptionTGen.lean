import Plausible.IR.Example

import Plausible.Gen
import Plausible.Sampleable
open Plausible

--------------------------------------------------------------------------
-- Helper functions (adapted from QuickChick sourcecode)
-- https://github.com/QuickChick/QuickChick/blob/master/src/Generators.v
--------------------------------------------------------------------------

/-- `pickDrop xs n` returns a weight & its generator `(k, gen)` such that `n < k`,
    and also returns the tail of the list after `(k, gen)` -/
def pickDrop (xs : List (Nat × OptionT Gen α)) (n : Nat) :=
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


/-- A handwritten generator for BSTs à la "Generating Good Generators for Inductive Relations"
   - We use the `OptionT` monad to add the possibility of failure to the `Gen` monad -/
def genBST (in1 : Nat) (in2 : Nat) : Nat → OptionT Gen Tree :=
  let rec aux_arb (size : Nat) (in1 : Nat) (in2 : Nat) : OptionT Gen Tree :=
    match size with
    | .zero => pure .Leaf
    | .succ size' =>
      backtrack [
        (1, pure .Leaf),
        (1, do
          let x ← Gen.choose Nat 0 in2 (by omega)
          if x > in1 then
            let l ← aux_arb size' in1 x
            let r ← aux_arb size' x in2
            pure (.Node x l r)
          else OptionT.fail)
      ]
  fun size => aux_arb size in1 in2

-- To sample from the generator, we have to do `OptionT.run` to extract the underlying generator,
-- then invoke `Gen.run` to display the generated value in the IO monad
def tempSize := 5
#eval (Gen.run (OptionT.run (genBST 1 10 tempSize)) tempSize)
