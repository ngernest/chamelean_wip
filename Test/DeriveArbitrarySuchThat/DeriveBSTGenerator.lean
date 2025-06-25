
import Plausible.Gen
import Plausible.New.OptionTGen
import Plausible.New.DecOpt
import Plausible.New.ArbitrarySizedSuchThat
import Plausible.New.DeriveGenerator

open ArbitrarySizedSuchThat OptionTGen

set_option guard_msgs.diff true

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

/--
info: Try this generator: instance : ArbitrarySizedSuchThat BinaryTree (fun t => BST lo hi t) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (lo_0 : Nat) (hi_0 : Nat) : OptionT Plausible.Gen BinaryTree :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1, OptionTGen.thunkGen (fun _ => pure BinaryTree.Leaf)), (1, OptionTGen.thunkGen (fun _ => OptionT.fail))]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1, OptionTGen.thunkGen (fun _ => pure BinaryTree.Leaf)),
            (Nat.succ size',
              OptionTGen.thunkGen
                (fun _ => do
                  let x ← Arbitrary.arbitrary
                  let l ← aux_arb initSize size' lo x
                  let r ← aux_arb initSize size' x hi
                  if lo < x && x < hi then ⏎
                    return BinaryTree.Node x l r
                  else
                    OptionT.fail))]
    fun size => aux_arb size size lo hi
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (t : BinaryTree) => BST lo hi t)
