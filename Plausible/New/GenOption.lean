import Plausible.IR.Example

import Plausible.Gen
import Plausible.Sampleable
open Plausible

------------------------
-- The GenOption monad
------------------------

/-- Type alias for Generators that produce a value wrapped in a `Option`
    (i.e. generators that may fail, i.e. because they ran out of fuel or because they failed to produce an inhabitant of `α`) -/
abbrev GenOption (α : Type) := Gen (Option α)

class ArbitraryOption (α : Type) where
  arbitrary : Gen (Option α)

/-- Pure: wrap a value in Some and lift to Gen -/
def genOptionPure {α : Type} (a : α) : Gen (Option α) :=
  pure (some a)

/-- Bind: extract the value if Some, otherwise propagate None -/
def genOptionBind {α β : Type} (g : GenOption α) (f : α → GenOption β) : Gen (Option β) := do
  let a_opt ← g
  match a_opt with
  | none => pure none
  | some a => f a

/-- `Monad` instance for `GenOption` -/
instance : Monad GenOption where
  pure := genOptionPure
  bind := genOptionBind

/-- Converts a `GenOption α` into a `GenOption β` using the function `f` -/
def genOptionMap {α β : Type} (f : α → β) (ga : GenOption α) : GenOption β :=
  ga >>= (pure ∘ f)

/-- `Functor` instance for `GenOption` -/
instance : Functor GenOption where
  map := genOptionMap

/-- Alias for a generator that always fails -/
def fail : Gen (Option α) :=
  return none

/-- Lifts a `Gen α` into a `Gen (Option α)`.
   (this allow us to use `Gen α` computations in places where `GenOption α` is expected) -/
def liftGenOption {α : Type} (g : Gen α) : Gen (Option α) :=
  g >>= (fun x => pure (some x))



--------------------------------------------------------------------------
-- Helper functions (adapted from QuickChick sourcecode)
-- https://github.com/QuickChick/QuickChick/blob/master/src/Generators.v
--------------------------------------------------------------------------

/-- `pickDrop xs n` returns a weight & its generator `(k, gen)` such that `n < k`,
    and also returns the tail of the list after `(k, gen)` -/
def pickDrop (xs : List (Nat × Gen (Option α))) (n : Nat)
  : Nat × Gen (Option α) × List (Nat × Gen (Option α)) :=
  match xs with
  | [] => (0, return none, [])
  | (k, x) :: xs =>
    if n < k then (k, x, xs)
    else
      let (k', x', xs') := pickDrop xs (n - k)
      (k', x', (k, x)::xs')

/-- Sums all the weights in an association list containing `Nat`s and `α`s -/
def sumFst (gs : List (Nat × α)) : Nat :=
  List.foldl (fun acc p => acc + p.fst) 0 gs

/-- Helper function for `backtrack` which picks generators with some initial amount of `fuel` -/
def backtrackFuel (fuel : Nat) (tot : Nat) (gs : List (Nat × Gen (Option α))) : Gen (Option α) :=
  match fuel with
  | .zero => pure .none
  | .succ fuel' => do
    let n ← Gen.choose Nat 0 (tot - 1) (by omega)
    let (k, g, gs') := pickDrop gs n
    let ma ← g
    match ma with
    | .some a => pure (.some a)
    | .none => backtrackFuel fuel' (tot - k) gs'

/-- Tries all generators until one returns a Some value or all failed once with None.
   The generators are picked at random according to their weights (like frequency), and each one is run at most once. -/
def backtrack (gs : List (Nat × Gen (Option α))) : Gen (Option α) :=
  backtrackFuel (gs.length) (sumFst gs) gs
