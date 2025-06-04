import Plausible.New.GenOption

import Plausible
open Plausible

/-- A datatype for binary trees -/
inductive BinaryTree where
  | Leaf : BinaryTree
  | Node : Nat → BinaryTree → BinaryTree → BinaryTree
  deriving Repr


/-- `BST lo hi t` describes whether a tree `t` is a BST that contains values strictly within `lo` and `hi` -/
inductive BST : Nat → Nat → BinaryTree → Prop where
  | BstLeaf: ∀ lo hi,
      BST lo hi .Leaf
  | BstNode: ∀ lo hi x l r,
      lo < x → x < hi →
      BST lo x l → BST x hi r →
      BST lo hi (.Node x l r)

/-- A generator for BSTs, where `in1` and `in2` correspond to `lo` and `hi`
    (modelled after the derived generator in the Generating Good Generators paper) -/
-- def genBST (in1 : Nat) (in2 : Nat) : Nat → GenOption BinaryTree :=
--   let rec aux_arb (size : Nat) (in1 : Nat) (in2 : Nat) : GenOption BinaryTree :=
--     match size with
--     | .zero => pure .Leaf
--     | .succ size' =>
--       backtrack [
--         ( 1, pure BinaryTree.Leaf ),
--         ( 1, do
--             let x ← Gen.choose Nat 0 in2 (by omega)
--             if x > in1 then
--               let l ← aux_arb size' in1 x
--               let r ← aux_arb size' x in2
--               pure (BinaryTree.Node x l r)
--             else fail )
--       ]
--   fun size => aux_arb size in1 in2
