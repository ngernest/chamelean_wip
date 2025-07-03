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


set_option trace.Meta.debug true



-- TODO: create a snapshot test for the `square_of` inductive relation

inductive square_of : Nat → Nat → Prop where
  | sq : forall n, square_of n (n * n)

#derive_checker (square_of n m)

/-
instance : DecOpt (square_of n m) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (n_0 : Nat) (m_0 : Nat) : Option Bool :=
      match size with
      | Nat.zero => DecOpt.checkerBacktrack [fun _ => DecOpt.andOptList [DecOpt.decOpt (@Eq Nat m (n * n)) initSize]]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack [fun _ => DecOpt.andOptList [DecOpt.decOpt (@Eq Nat m (n * n)) initSize]]
    fun size => aux_dec size size n m

-/



---

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
