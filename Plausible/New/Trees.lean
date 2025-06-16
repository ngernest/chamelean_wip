/-- A datatype for binary trees -/
inductive Tree where
  | Leaf : Tree
  | Node : Nat → Tree → Tree → Tree
  deriving Repr

/-- `BST lo hi t` describes whether a tree `t` is a BST that contains values strictly within `lo` and `hi` -/
inductive BST : Nat → Nat → Tree → Prop where
  | BstLeaf: ∀ lo hi,
      BST lo hi .Leaf
  | BstNode: ∀ lo hi x l r,
      lo < x → x < hi →
      BST lo x l → BST x hi r →
      BST lo hi (.Node x l r)
