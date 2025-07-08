import Plausible.New.DecOpt
import Plausible.New.DeriveChecker
import Test.DeriveDecOpt.DeriveBSTChecker
import Test.DeriveArbitrarySuchThat.DeriveBalancedTreeGenerator

open DecOpt

set_option guard_msgs.diff true

/--
info: Try this checker: instance : DecOpt (balancedTree n t) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (n_1 : Nat) (t_1 : BinaryTree) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match n_1, t_1 with
            | 0, BinaryTree.Leaf => Option.some Bool.true
            | _, _ => Option.some Bool.false,
            fun _ =>
            match n_1, t_1 with
            | 1, BinaryTree.Leaf => Option.some Bool.true
            | _, _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match n_1, t_1 with
            | 0, BinaryTree.Leaf => Option.some Bool.true
            | _, _ => Option.some Bool.false,
            fun _ =>
            match n_1, t_1 with
            | 1, BinaryTree.Leaf => Option.some Bool.true
            | _, _ => Option.some Bool.false,
            fun _ =>
            match n_1, t_1 with
            | Nat.succ n, BinaryTree.Node x l r =>
              DecOpt.andOptList [aux_dec initSize size' n l, aux_dec initSize size' n r]
            | _, _ => Option.some Bool.false]
    fun size => aux_dec size size n t
-/
#guard_msgs(info, drop warning) in
#derive_checker (balancedTree n t)
