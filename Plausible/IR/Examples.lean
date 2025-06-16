import Lean
open Nat

/-- Dummy inductive relation for testing purposes -/
inductive RGB where
| Red : RGB
| Green : RGB
| Blue : RGB

/-- A datatype for binary trees -/
inductive Tree where
| Leaf : Tree
| Node : Nat → Tree → Tree → Tree
deriving Repr

/-- `balanced n t` describes whether the tree `t` of height `n` is *balanced*, i.e.
    every path through the tree has length either `n` or `n-1`. -/
inductive balanced : Nat → Tree → Prop where
| B0 : balanced 0 .Leaf
| B1 : balanced 1 .Leaf
| BS : ∀ n x Γ r,
  balanced n Γ → balanced n r →
  balanced (succ n) (.Node x Γ r)

/-- `bst lo hi t` describes whether a tree `t` is a BST that contains values strictly within `lo` and `hi` -/
inductive bst : Nat → Nat → Tree → Prop where
| BstLeaf: bst lo hi .Leaf
| BstNode: ∀ lo hi x Γ r, lo < x → x < hi → bst lo x Γ →  bst x hi r → bst lo hi (Tree.Node x Γ r)

/-- Base types in the STLC (either Nat or functions) -/
inductive type where
| Nat : type
| Fun: type → type → type
deriving BEq, Repr

/-- Datatype for expressions in the STLC extended with naturals and addition -/
inductive term where
| Const: Nat → term
| Add: term → term → term
| Var: Nat → term
| App: term → term → term
| Abs: type → term → term
deriving BEq, Repr

/- `typing Γ e τ` is the typing judgement `Γ ⊢ e : τ`.
    For simplicity, we only include `TConst` and `TAdd` for now (the other cases require auxiliary `inductive`s) -/
inductive typing: List type → term → type → Prop where
| TConst : ∀ n, typing Γ (.Const n) .Nat
| TAdd: ∀ e1 e2, typing Γ e1 .Nat → typing Γ e2 .Nat → typing Γ (term.Add e1 e2) .Nat
| TAbs: ∀ e t1 t2, typing (t1::L) e t2 → typing Γ (term.Abs t1 e) (.Fun t1 t2)
| TVar: ∀ x t, typing Γ (term.Var x) t
| TApp: ∀ e1 e2 t1 t2, typing Γ e2 t1 → typing Γ e1 (.Fun t1 t2) → typing Γ (term.App e1 e2) t2
