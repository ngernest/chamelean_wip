import Plausible.New.DeriveGenerator
import Plausible.Gen

import Plausible.New.OptionTGen
import Plausible.New.DecOpt
import Plausible.New.ArbitrarySizedSuchThat
import Plausible.New.STLC


open ArbitrarySizedSuchThat OptionTGen

/-- Dummy inductive relation for testing purposes -/
inductive RGB where
| Red
| Green
| Blue

inductive Value where
  | none
  | bool (value : Bool)
  | int (value : Int)
  | tensor (shape : List Nat) (dtype : String)

def tensorValue : Value := .tensor (dtype := "hello") (shape := [0])

inductive MyList (α : Type) where
  | Nil
  | Cons (x : α) (xs : MyList α)

#derive_arbitrary Value


/- Example usage:
  ```
  #derive_generator (fun (<name of generated value> : <type of generated value>) => <inductive relation applied to all args>)
  ```
  This produces an instance of the `ArbitrarySizedSuchThat` typeclass, which contains a generator for values satisfying the inductive
  relation. See examples below:

  (Note: you may need to comment out the typeclass instances in `Trees.lean` if Lean complains about overlapping instances.)
-/


-- #derive_generator (fun (t : Tree) => balanced n t)
-- #derive_generator (fun (t : Tree) => bst lo hi t)

-- TODO: update derived generator to use this template
-- def aux_arb a1 a2 size :=
--   match size with
--   | .zero => pick from a1
--   | .succ size' => pick from a2

-- instance : ArbitrarySizedSuchThat Tree (fun t => bst lo hi t) where
--   arbitrarySizedST :=
--      fun size => aux_arb [gen_balance_fail, gen_balance_1] [gen_balance_2] size
--       where
--         gen_balance_fail := OptionTGen.thunkGen (fun _ => OptionT.fail)
--         gen_balance_1 := OptionTGen.thunkGen (fun _ => pure Tree.Leaf)
--         gen_balance_2 := ...


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
-- #eval runSizedGen (arbitrarySizedST (fun t => balanced 5 t))


-- Work in progress: extend generator deriver to handle STLC example
-- TODO: figure out issue with `TApp` in the derived generator for `typing`
-- TODO: figure out how to handle checkers
-- #derive_generator (fun (x : Nat) => lookup Γ x τ)


-- #derive_generator (fun (e : term) => typing Γ e τ)
