import Lean
open Nat



inductive Tree  where
| Leaf : Nat → Tree
| Node : Nat → Tree  → Tree  → Tree
deriving Repr

inductive balanced : Nat → Tree → Prop where
| B0 : ∀ x, balanced 0 (Tree.Leaf x)
| BS : ∀ n x l r, balanced n l → balanced n r → balanced (succ n) (Tree.Node x l r)

inductive bst : Nat → Nat → Tree → Prop where
| BstLeaf: ∀ lo hi x, lo < x → x < hi → bst lo hi (Tree.Leaf x)
| BstNode: ∀ lo hi x l r, lo < x → x < hi → bst lo x l →  bst x hi r → bst lo hi (Tree.Node x l r)

inductive type where
| N : type
| Arr: type → type → type
deriving BEq, Repr

inductive term  where
| Con: Nat → term
| Add: term → term → term
| Var: Nat → term
| App: term → term → term
| Abs: type → term → term
deriving BEq, Repr

inductive typing: List type →  term → type → Prop where
| TCon : ∀ n, typing L (term.Con n) type.N
| TAdd: ∀ e1 e2, typing L e1 type.N →  typing L e2 type.N  →  typing L (term.Add e1 e2) type.N
| TAbs: ∀ e t1 t2, typing (t1::L) e t2 → typing L (term.Abs t1 e) (type.Arr t1 t2)
--| TVar: ∀ x t, typing L (term.Var x) t
| TApp: ∀ e1 e2 t1 t2, typing L e2 t1 → typing L e1 (type.Arr t1 t2) → typing L (term.App e1 e2) t2


