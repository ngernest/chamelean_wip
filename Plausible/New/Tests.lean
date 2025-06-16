import Plausible.New.DeriveGenerator
import Plausible.Gen

import Plausible.New.OptionTGen
open OptionTGen
open Lean Elab Command

-- Example usage:
-- #derive_generator (fun (t : Tree) => bst lo hi t)
-- #derive_generator (fun (t : Tree) => balanced n t)

/-
(Note: this is not the most efficient generator -- ideally we would be able to push the if-expression that checks
whether `lo < x < hi` immediately after we generate `x` so that the generator can fail quickly if `x` is out of bounds.
We can make this generator more efficient using Segev's generator schedules.)
-/

-- One can inspect the type of the derived generator like so:
-- #check gen_bst

-- To sample from the generator, we have to do `OptionT.run` to extract the underlying generator,
-- then invoke `Gen.run` to display the generated value in the IO monad
-- #eval runSizedGen (gen_bst 1 10) 10




-- Work in progress: extend generator deriver to handle STLC example
-- TODO: figure out how to handle checkers
-- TODO: add `init_size` parameter to derived generators (serves as fuel when invoking other generators)
-- #derive_generator (fun (e : term) => typing Γ e τ)
