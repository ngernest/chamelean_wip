import Plausible.New.DeriveGenerator
import Plausible.Gen

import Plausible.New.OptionTGen
import Plausible.New.DecOpt
import Plausible.New.Arbitrary
import Plausible.New.ArbitrarySizedSuchThat
import Plausible.New.EnumeratorCombinators
import Plausible.New.DeriveEnum
import Plausible.New.DeriveChecker
import Plausible.New.STLC

import Lean
open Lean Meta

open Plausible ArbitrarySizedSuchThat OptionTGen

-- TODO: figure out how to write functions
-- #derive_checker (typing Γ e τ)

/- A handwritten checker which checks `typing Γ e τ`, ignoring the case for `App`
    (based on the auto-derived checker produced by QuickChick) -/
-- def checkTypingAlt (Γ : List type) (e : term) (τ : type) : Nat → OptionT Id Bool :=
--   let rec aux_dec (initSize : Nat) (size : Nat) (Γ : List type) (e : term) (τ : type) : OptionT Id Bool :=
--     match size with
--     | .zero => DecOpt.checkerBacktrack []
--     | .succ size' =>
--       DecOpt.checkerBacktrackAlt [
--         fun _ =>
--           match e with
--           | .App e1 e2 => do
--             let t1 ← EnumSuchThat.enumST (fun τ => typing Γ e2 τ)
--             let _ ← aux_dec initSize size' Γ e1 (.Fun t1 τ)
--             return true
--           | _ => some false
--       ]
--   fun size => aux_dec size size Γ e τ


/- Example usage:
  ```
  #derive_generator (fun (<name of generated value> : <type of generated value>) => <inductive relation applied to all args>)
  ```
  This produces an instance of the `ArbitrarySizedSuchThat` typeclass, which contains a generator for values satisfying the inductive
  relation. See examples below:


-/


-- #derive_generator (fun (t : Tree) => balanced n t)
-- #derive_generator (fun (t : Tree) => bst lo hi t)

/-
(Note: this is not the most efficient generator -- ideally we would be able to push the if-expression that checks
whether `lo < x < hi` immediately after we generate `x` so that the generator can fail quickly if `x` is out of bounds.
We can make this generator more efficient using Segev's generator schedules.)
-/


/-
To sample from the derived generator, we apply the `arbitrarySizedST` function
(from the `ArbitrarySizedSuchThat` typeclass) onto the proposition that constrains
the generated values (e.g. `fun t => balanced 5 t` for balanced trees of height 5).
We then invoke `runSizedGen` to display the generated value in the `IO` monad.

For example:
-/

-- def tempSize := 10
-- #eval runSizedGen (GenSizedSuchThat.genSizedST (fun t => balanced 5 t)) tempSize


-- Work in progress: extend generator deriver to handle STLC example
-- TODO: figure out issue with `TApp` in the derived generator for `typing`
-- TODO: figure out how to handle checkers

-- #derive_arbitrary term
-- #derive_generator (fun (e : term) => typing Γ e τ)
