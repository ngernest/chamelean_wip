import Plausible.New.DecOpt
import Plausible.New.DeriveChecker
import Test.DeriveArbitrarySuchThat.DeriveBSTGenerator

open DecOpt

set_option guard_msgs.diff true

/--
info: Try this checker: instance : DecOpt (Between lo x hi) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (lo_1 : Nat) (x_1 : Nat) (hi_1 : Nat) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match x_1, hi_1 with
            | Nat.succ lo_1_0, Nat.succ (Nat.succ m) => DecOpt.decOpt (@LE.le Nat instLENat lo_1 m) initSize
            | _, _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match x_1, hi_1 with
            | Nat.succ lo_1_0, Nat.succ (Nat.succ m) => DecOpt.decOpt (@LE.le Nat instLENat lo_1 m) initSize
            | _, _ => Option.some Bool.false,
            fun _ =>
            match x_1, hi_1 with
            | Nat.succ m, Nat.succ o => aux_dec initSize size' lo_1 m o
            | _, _ => Option.some Bool.false]
    fun size => aux_dec size size lo x hi
-/
#guard_msgs(info, drop warning) in
#derive_checker (Between lo x hi)

/--
info: Try this checker: instance : DecOpt (BST lo hi t) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (lo_1 : Nat) (hi_1 : Nat) (t_1 : BinaryTree) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match t_1 with
            | BinaryTree.Leaf => Option.some Bool.true
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match t_1 with
            | BinaryTree.Leaf => Option.some Bool.true
            | _ => Option.some Bool.false,
            fun _ =>
            match t_1 with
            | BinaryTree.Node x l r =>
              DecOpt.andOptList
                [DecOpt.decOpt (Between lo_1 x hi_1) initSize, aux_dec initSize size' lo_1 x l,
                  aux_dec initSize size' x hi_1 r]
            | _ => Option.some Bool.false]
    fun size => aux_dec size size lo hi t
-/
#guard_msgs(info, drop warning) in
#derive_checker (BST lo hi t)
