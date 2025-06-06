import Plausible.New.DeriveGenerator
import Plausible.New.GenOption
import Plausible.Gen

import Plausible.New.OptionTGen
open OptionTGen


-- Example usage:
-- (Note: we require users to explicitly provide a type annotation to the argument to the lambda)

#derive_generator (fun (t : Tree) => balanced n t)
#check gen_balanced
#eval runSizedGen (gen_balanced 2) 10

-- #derive_generator (fun (t : Tree) => bst lo hi t)
-- #derive_generator (fun (e : term) => typing Γ e τ)
