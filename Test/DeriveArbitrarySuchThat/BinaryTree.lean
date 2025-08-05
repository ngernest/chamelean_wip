/-- A datatype for binary trees. This type definition is used in the following test files:
   - `DeriveBalancedTreeGenerator.lean`
   - `DeriveBSTGenerator.lean`
   - `NonLinearPatternsTest.lean` -/
inductive BinaryTree where
  | Leaf : BinaryTree
  | Node : Nat → BinaryTree → BinaryTree → BinaryTree
  deriving Repr
