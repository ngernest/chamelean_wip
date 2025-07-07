import Plausible.New.DeriveGenerator
import Plausible.Gen

import Plausible.New.OptionTGen
import Plausible.New.DecOpt
import Plausible.New.Arbitrary
import Plausible.New.Enumerators
import Plausible.New.ArbitrarySizedSuchThat
import Plausible.New.EnumeratorCombinators
import Plausible.New.DeriveEnum
import Plausible.New.DeriveChecker
import Plausible.New.STLC

import Lean
open Lean Meta

open Plausible ArbitrarySizedSuchThat OptionTGen

deriving instance Enum for Tree

instance : EnumSizedSuchThat Tree (fun t => bst lo hi t) where
  enumSizedST :=
   let rec aux_enum (initSize : Nat) (size : Nat) (lo_0 : Nat) (hi_0 : Nat) : OptionT Enumerator Tree :=
      match size with
      | Nat.zero =>
        EnumeratorCombinators.enumerate
          [pure .Leaf, OptionT.fail]
      | Nat.succ size' =>
        EnumeratorCombinators.enumerate
          [pure .Leaf,
            do
              let x ← Enum.enum
              let l ← aux_enum initSize size' lo_0 x
              let r ← aux_enum initSize size' x hi_0
              if lo < x && x < hi then
                return Tree.Node x l r
              else
                OptionT.fail]
    fun size => aux_enum size size lo hi




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
