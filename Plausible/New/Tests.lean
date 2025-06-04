import Plausible.New.DeriveGenerator
import Plausible.New.GenOption
import Plausible.Gen

-- Example usage:
-- (Note: we require users to explicitly provide a type annotation to the argument to the lambda)

-- #derive_generator (fun (x : Nat) => RGB)

#derive_generator (fun (t : Tree) => bst lo hi t)
#print gen_bst




#derive_generator (fun (e : term) => typing Γ e τ)
