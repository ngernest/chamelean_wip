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
#derive_generator (fun (t : Tree) => bst lo hi t)

-- One can inspect the type of the derived generator like so:
-- #check gen_bst

-- To sample from the generator, we have to do `OptionT.run` to extract the underlying generator,
-- then invoke `Gen.run` to display the generated value in the IO monad
-- #eval runSizedGen (gen_bst 1 10) 10


-- Some other examples:
-- TODO: figure out how to pattern match on the argument `n` when generating Leafs for height 0
-- #derive_generator (fun (t : Tree) => balanced n t)

-- #derive_generator (fun (e : term) => typing Γ e τ)
