import Plausible.New.DecOpt
import Plausible.New.DeriveChecker
import Test.DeriveDecOpt.DeriveBSTChecker
import Test.DeriveArbitrarySuchThat.NonLinearPatternsTest

open DecOpt

set_option guard_msgs.diff true

-- TODO: (fix this)
-- we want to invoke `in2_0 = in1_0` in the checker, not `in1 = in1_0`!

/--
info: Try this checker: instance : DecOpt (GoodTree in1 in2 t) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (in1_0 : Nat) (in2_0 : Nat) (t_0 : BinaryTree) : Option Bool :=
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
            | _ => Option.some Bool.false]
    fun size => aux_dec size size in1 in2 t
-/
#guard_msgs(info, drop warning) in
#derive_checker (GoodTree in1 in2 t)
