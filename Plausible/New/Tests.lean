import Plausible.New.DeriveGenerator
import Plausible.Gen

import Plausible.New.OptionTGen
import Plausible.New.DecOpt
import Plausible.New.Arbitrary
import Plausible.New.ArbitrarySizedSuchThat
import Plausible.New.STLC


open Plausible ArbitrarySizedSuchThat OptionTGen

/-- Dummy inductive relation for testing purposes -/
inductive RGB where
  | Red
  | Green
  | Blue
  deriving Arbitrary

inductive Value where
  | none
  | bool (b : Bool)
  | int (i : Int)
  | tensor (shape : List Nat) (dtype : String)
  deriving Arbitrary

inductive Foo where
  | FromBitVec : ∀ (n : Nat), BitVec n → String → Foo
  deriving Arbitrary

-- #eval runArbitrary (α := Foo) 10

inductive MyList where
  | Nil
  | Cons (x : Nat) (xs : MyList)

inductive MyListAnon where
  | Nil : MyListAnon
  | Cons : Nat -> MyListAnon -> MyListAnon

-- #derive_arbitrary MyListAnon

-- #derive_arbitrary Tree
-- #derive_arbitrary type
-- #derive_arbitrary term
-- #derive_arbitrary Value

-- #eval runArbitrary (α := MyList) 10



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
