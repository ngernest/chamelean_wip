import Plausible.New.DeriveGenerator
import Plausible.New.GenOption
import Plausible.Gen

-- Example usage:
-- (Note: we require users to explicitly provide a type annotation to the argument to the lambda)

#derive_generator (fun (t : Tree) => bst lo hi t)
#derive_generator (fun (e : term) => typing Γ e τ)


/- A generator for BSTs, where `in1` and `in2` correspond to `lo` and `hi`
    (modelled after the derived generator in the Generating Good Generators paper) -/
-- def genBST (in1 : Nat) (in2 : Nat) : Nat → GenOption Tree :=
--   let rec aux_arb (size : Nat) (in1 : Nat) (in2 : Nat) : GenOption Tree :=
--     match size with
--     | .zero => pure .Leaf
--     | .succ size' =>
--       backtrack [
--         ⟨ 1, pure Tree.Leaf ⟩,
--         ⟨ 1, do
--             let x ← liftGenOption (Gen.choose Nat 0 in2 (by omega))
--             if x > in1 then
--               let l ← aux_arb size' in1 x
--               let r ← aux_arb size' x in2
--               pure (Tree.Node x l r)
--             else fail⟩
--       ]
--   fun size => aux_arb size in1 in2
