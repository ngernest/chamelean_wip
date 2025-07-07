import Plausible.New.DecOpt
import Plausible.New.Enumerators
import Plausible.New.DeriveEnumSuchThat
import Plausible.New.EnumeratorCombinators
import Test.DeriveEnumSuchThat.DeriveBSTEnumerator

-- See `Test/DeriveArbitrarySuchThat/NonLinearPatternsTest.lean` for the definition of the inductive relations
import Test.DeriveArbitrarySuchThat.NonLinearPatternsTest

set_option guard_msgs.diff true

-- TODO: (fix this)
-- we want to invoke `in2_0 = in1_0` in the enumerator, not `in1 = in1_0`!

/--
info: Try this generator: instance : EnumSizedSuchThat BinaryTree (fun t => GoodTree in1 in2 t) where
  enumSizedST :=
    let rec aux_enum (initSize : Nat) (size : Nat) (in1_0 : Nat) (in2_0 : Nat) : OptionT Enumerator BinaryTree :=
      match size with
      | Nat.zero =>
        EnumeratorCombinators.enumerate
          [match DecOpt.decOpt (in1 = in1_0) initSize with
            | Option.some Bool.true => pure BinaryTree.Leaf
            | _ => OptionT.fail,
            OptionT.fail]
      | Nat.succ size' =>
        EnumeratorCombinators.enumerate
          [match DecOpt.decOpt (in1 = in1_0) initSize with
            | Option.some Bool.true => pure BinaryTree.Leaf
            | _ => OptionT.fail]
    fun size => aux_enum size size in1 in2
-/
#guard_msgs(info, drop warning) in
#derive_enumerator (fun (t : BinaryTree) => GoodTree in1 in2 t)
