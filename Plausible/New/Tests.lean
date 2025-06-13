import Plausible.New.DeriveGenerator
import Plausible.New.GenOption
import Plausible.Gen

import Plausible.New.OptionTGen
open OptionTGen
open Lean Elab Command

-- Example usage:
-- (Note: we require users to explicitly provide a type annotation to the argument to the lambda)
-- Click on the VS Code sidebar to insert the code of the derived generator into the Lean file

-- Some examples:
-- #derive_generator (fun (t : Tree) => bst lo hi t)

/-
The following generator is derived:
```
def gen_bst (lo : Nat) (hi : Nat) : Nat → OptionT Plausible.Gen Tree :=
  let rec aux_arb (size : Nat) (lo : Nat) (hi : Nat) : OptionT Plausible.Gen Tree :=
    match size with
    | Nat.zero =>
      OptionTGen.backtrack
        [(1, OptionTGen.thunkGen (fun _ => pure Tree.Leaf)), (1, OptionTGen.thunkGen (fun _ => OptionT.fail))]
    | Nat.succ size' =>
      OptionTGen.backtrack
        [(1, OptionTGen.thunkGen (fun _ => pure Tree.Leaf)),
          (Nat.succ size',
            OptionTGen.thunkGen
              (fun _ => do
                let x ← Plausible.SampleableExt.interpSample Nat
                let l ← aux_arb size' lo x
                let r ← aux_arb size' x hi
                if lo < x && x < hi then
                  return Tree.Node x l r
                else
                  OptionT.fail))]
  fun size => aux_arb size lo hi
```
(Note: this is not the most efficient generator -- ideally we would be able to push the if-expression that checks
whether `lo < x < hi` immediately after we generate `x` so that the generator can fail quickly if `x` is out of bounds.)
-/

-- One can inspect the type of the derived generator like so:
-- #check gen_bst

-- To sample from the generator, we have to do `OptionT.run` to extract the underlying generator,
-- then invoke `Gen.run` to display the generated value in the IO monad
-- #eval runSizedGen (gen_bst 1 10) 10


-- Some other examples:
-- TODO: figure out how to pattern match on the argument `n` when generating Leafs for height 0
-- TODO: uncomment Thanh's code for the BST example and try it out on the `balanced` example
-- #derive_generator (fun (t : Tree) => balanced n t)

-- TODO: figure out how to handle dependencies (references to other inductive relations) for the `typing` example
-- #derive_generator (fun (e : term) => typing Γ e τ)
