import Plausible.New.DeriveGenerator
import Plausible.Gen

import Plausible.New.OptionTGen
import Plausible.New.DecOpt
import Plausible.New.GenSizedSuchThat
import Plausible.New.STLC


open GenSizedSuchThat OptionTGen

/- Example usage:
  ```
  #derive_generator (fun (<name of generated value> : <type of generated value>) => <inductive relation applied to all args>)
  ```
  This produces an instance of the `GenSizedSuchThat` typeclass, which contains a generator for values satisfying the inductive
  relation. See examples below:

  (Note: you may need to comment out the typeclass instances in `Trees.lean` if Lean complains about overlapping instances.)
-/

-- #derive_generator (fun (t : Tree) => bst lo hi t)
-- #derive_generator (fun (t : Tree) => balanced n t)

/-
(Note: this is not the most efficient generator -- ideally we would be able to push the if-expression that checks
whether `lo < x < hi` immediately after we generate `x` so that the generator can fail quickly if `x` is out of bounds.
We can make this generator more efficient using Segev's generator schedules.)
-/


/-
To sample from the derived generator, we apply the `genSizedST` function
(from the `GenSizedSuchThat` typeclass) onto the proposition that constrains
the generated values (e.g. `fun t => balanced 5 t` for balanced trees of height 5).
We then invoke `runSizedGen` to display the generated value in the `IO` monad.

For example:
-/

-- def tempSize := 10
-- #eval runSizedGen (genSizedST (fun t => balanced 5 t)) tempSize


-- Work in progress: extend generator deriver to handle STLC example
-- TODO: change the call to `aux_arb` for lookup into a call to the appropriate typeclass method
-- ^^ TODO: add typeclass stuff?
-- TODO: figure out how to handle checkers
-- #derive_generator (fun (x : Nat) => lookup Γ x τ)
-- #derive_generator (fun (e : term) => typing Γ e τ)
