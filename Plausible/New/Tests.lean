import Plausible.New.DeriveGenerator
import Plausible.New.GenOption
import Plausible.Gen

/-- Binary trees containing a `Nat` at each node -/
inductive Tree where
  | Leaf : Tree
  | Node : Nat → Tree → Tree → Tree
  deriving Repr

/-- `bst lo hi t` describes whether a tree `t` is a BST that contains values strictly within `lo` and `hi` -/
inductive bst : Nat → Nat → Tree → Prop where
  | BstLeaf: ∀ lo hi,
      bst lo hi .Leaf
  | BstNode: ∀ lo hi x l r,
      lo < x → x < hi →
      bst lo x l → bst x hi r →
      bst lo hi (.Node x l r)

/-- Base types in the STLC (either Nat or functions) -/
inductive type where
  | Nat : type
  | Arr : type → type → type
  deriving BEq, Repr

/-- Terms in the STLC w/ naturals, where variables are represented using De Bruijn indices -/
inductive term where
  | Const : Nat → term
  | Add : term → term → term
  | Var : Nat → term
  | App : term → term → term
  | Abs : type → term → term
  deriving BEq, Repr

/- `typing Γ e τ` is the typing judgement `Γ ⊢ e : τ`.
    For simplicity, we only include `TConst` and `TAdd` for now (the other cases require auxiliary `inductive`s) -/
inductive typing (Γ : List type) : term → type → Prop where
  | TConst : ∀ n, typing Γ (.Const n) type.Nat
  | TAdd: ∀ e1 e2, typing Γ e1 .Nat → typing Γ e2 .Nat → typing Γ (term.Add e1 e2) .Nat

-- Example usage:
-- (Note: we require users to explicitly provide a type annotation to the argument to the lambda)

-- #derive_generator (fun (t : Tree) => bst lo hi t)
-- #derive_generator (fun (e : term) => typing Γ e τ)


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
