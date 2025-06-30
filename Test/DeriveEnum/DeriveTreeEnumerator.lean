import Plausible.New.Enumerators
import Plausible.New.EnumeratorCombinators
import Plausible.New.DeriveEnum
import Plausible.IR.Examples

set_option guard_msgs.diff true

-- Invoke deriving instance handler for the `Arbitrary` typeclass on `type` and `term`
deriving instance Enum for Tree

-- Test that we can successfully synthesize instances of `Arbitrary` & `ArbitrarySized`

/-- info: instEnumSizedTree_test -/
#guard_msgs in
#synth EnumSized Tree

/-- info: instEnumOfEnumSized -/
#guard_msgs in
#synth Enum Tree

-- We test the command elaborator frontend in a separate namespace to
-- avoid overlapping typeclass instances for the same type
namespace CommandElaboratorTest

/--
info: Try this enumerator: instance : EnumSized Tree where
  enumSized :=
    let rec aux_enum (size : Nat) : Enumerator Tree :=
      match size with
      | Nat.zero => EnumeratorCombinators.oneOfWithDefault (pure Tree.Leaf) [pure Tree.Leaf]
      | Nat.succ size' =>
        EnumeratorCombinators.oneOfWithDefault (pure Tree.Leaf)
          [pure Tree.Leaf, do
            let a_0 ← Enum.enum
            let a_1 ← aux_enum size'
            let a_2 ← aux_enum size'
            return Tree.Node a_0 a_1 a_2]
    fun size => aux_enum size
-/
#guard_msgs(info, drop warning) in
#derive_enum Tree

end CommandElaboratorTest
