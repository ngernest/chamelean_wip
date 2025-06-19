
import Plausible.Gen
import Plausible.New.OptionTGen
import Plausible.New.DecOpt
import Plausible.New.GenSizedSuchThat
import Plausible.New.DeriveGenerator

open GenSizedSuchThat OptionTGen

/-- A datatype for binary trees -/
inductive BinaryTree where
  | Leaf : BinaryTree
  | Node : Nat → BinaryTree → BinaryTree → BinaryTree
  deriving Repr

/-- `BST lo hi t` describes whether a tree `t` is a BST that contains values strictly within `lo` and `hi` -/
inductive BST : Nat → Nat → BinaryTree → Prop where
  | BstLeaf: BST lo hi .Leaf
  | BstNode: ∀ lo hi x l r,
    lo < x →
    x < hi →
    BST lo x l →
    BST x hi r →
    BST lo hi (.Node x l r)

-- Invoke generator
#derive_generator (fun (t : Tree) => BST lo hi t)

-- TODO: figure out how to print out the generated code to an `.out` file
-- TODO: set up Turnt
