import Plausible.New.DeriveGenerator
import Plausible.New.GenOption
import Plausible.Gen

import Plausible.New.OptionTGen
open OptionTGen


-- Example usage:
-- (Note: we require users to explicitly provide a type annotation to the argument to the lambda)
-- Click on the VS Code sidebar to insert the code of the derived generator into the Lean file
def gen_balanced (n : Nat) : Nat → OptionT Plausible.Gen Tree :=
  let rec aux_arb (size : Nat) (n : Nat) : OptionT Plausible.Gen Tree :=
    match size with
    | Nat.zero =>
      OptionTGen.backtrack
        [(1, OptionTGen.thunkGen (fun _ => pure Tree.Leaf)), (1, OptionTGen.thunkGen (fun _ => pure Tree.Leaf)),
          (1, OptionTGen.thunkGen (fun _ => OptionT.fail))]
    | Nat.succ size' =>
      OptionTGen.backtrack
        [(1, OptionTGen.thunkGen (fun _ => pure Tree.Leaf)), (1, OptionTGen.thunkGen (fun _ => pure Tree.Leaf)),
          (1, OptionTGen.thunkGen (fun _ => OptionT.fail))]
  fun size => aux_arb size n

-- One can inspect the type of the derived generator like so:
-- #check gen_balanced

-- To sample from the generator, we have to do `OptionT.run` to extract the underlying generator,
-- then invoke `Gen.run` to display the generated value in the IO monad
-- #eval runSizedGen (gen_balanced 2) 10

-- Some other examples:
-- #derive_generator (fun (t : Tree) => bst lo hi t)
-- #derive_generator (fun (e : term) => typing Γ e τ)
