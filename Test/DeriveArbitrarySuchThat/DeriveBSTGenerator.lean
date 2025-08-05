
import Plausible.Gen
import Plausible.New.OptionTGen
import Plausible.New.DecOpt
import Plausible.New.ArbitrarySizedSuchThat
import Plausible.GeneratingGoodGenerators.DeriveSubGenerator
import Test.DeriveArbitrarySuchThat.BinaryTree

open ArbitrarySizedSuchThat OptionTGen

set_option guard_msgs.diff true


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
info: Try this generator: instance : ArbitrarySizedSuchThat BinaryTree (fun t_1 => BST lo_1 hi_1 t_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (lo_1 : Nat) (hi_1 : Nat) : OptionT Plausible.Gen BinaryTree :=
      match size with
      | Nat.zero => OptionTGen.backtrack [(1, return BinaryTree.Leaf)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1, return BinaryTree.Leaf),
            (Nat.succ size', do
              let x ← ArbitrarySizedSuchThat.arbitrarySizedST (fun x => LT.lt lo_1 x) initSize;
              match DecOpt.decOpt (LT.lt x hi_1) size with
                | Option.some Bool.true => do
                  let l ← ArbitrarySizedSuchThat.arbitrarySizedST (fun l => BST lo_1 x l) initSize;
                  do
                    let r ← ArbitrarySizedSuchThat.arbitrarySizedST (fun r => BST x hi_1 r) initSize;
                    return BinaryTree.Node x l r
                | _ => OptionT.fail)]
    fun size => aux_arb size size lo_1 hi_1
-/
#guard_msgs(info, drop warning) in
#derive_scheduled_generator (fun (t : BinaryTree) => BST lo hi t)
