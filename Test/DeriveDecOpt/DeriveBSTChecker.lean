import Plausible.New.DecOpt
import Plausible.New.DeriveChecker
import Test.DeriveArbitrarySuchThat.DeriveBSTGenerator

open DecOpt

set_option guard_msgs.diff true

/--
info: Try this checker: instance : DecOpt (BST lo hi t) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (lo_0 : Nat) (hi_0 : Nat) (t_0 : BinaryTree) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match t_0 with
            | BinaryTree.Leaf => Option.some Bool.true
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match t_0 with
            | BinaryTree.Leaf => Option.some Bool.true
            | _ => Option.some Bool.false,
            fun _ =>
            match t_0 with
            | BinaryTree.Node x l r =>
              DecOpt.andOptList
                [DecOpt.decOpt (@LT.lt Nat instLTNat lo x) initSize, DecOpt.decOpt (@LT.lt Nat instLTNat x hi) initSize,
                  aux_dec initSize size' lo x l, aux_dec initSize size' x hi r]
            | _ => Option.some Bool.false]
    fun size => aux_dec size size lo hi t
-/
#guard_msgs(info, drop warning) in
#derive_checker (BST lo hi t)
