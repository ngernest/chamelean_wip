import Plausible.Chamelean.Enumerators
import Plausible.Chamelean.EnumeratorCombinators
import Plausible.Chamelean.DeriveEnum
import Test.DeriveArbitrary.DeriveNKIValueGenerator

deriving instance Enum for Value

set_option guard_msgs.diff true

-- Test that we can successfully synthesize instances of `Arbitrary` & `ArbitrarySized`

/-- info: instEnumSizedValue -/
#guard_msgs in
#synth EnumSized Value

/-- info: instEnumOfEnumSized -/
#guard_msgs in
#synth Enum Value

-- We test the command elaborator frontend in a separate namespace to
-- avoid overlapping typeclass instances for the same type
namespace CommandElaboratorTest

/--
info: Try this enumerator: instance : EnumSized Value where
  enumSized :=
    let rec aux_enum (size : Nat) : Enumerator Value :=
      match size with
      | Nat.zero =>
        EnumeratorCombinators.oneOfWithDefault (pure Value.none)
          [pure Value.none, do
            let value_0 ← Enum.enum
            return Value.bool value_0, do
            let value_0 ← Enum.enum
            return Value.int value_0, do
            let value_0 ← Enum.enum
            return Value.string value_0, pure Value.ellipsis, do
            let shape_0 ← Enum.enum
            let dtype_0 ← Enum.enum
            return Value.tensor shape_0 dtype_0]
      | Nat.succ size' =>
        EnumeratorCombinators.oneOfWithDefault (pure Value.none)
          [pure Value.none, do
            let value_0 ← Enum.enum
            return Value.bool value_0, do
            let value_0 ← Enum.enum
            return Value.int value_0, do
            let value_0 ← Enum.enum
            return Value.string value_0, pure Value.ellipsis, do
            let shape_0 ← Enum.enum
            let dtype_0 ← Enum.enum
            return Value.tensor shape_0 dtype_0, ]
    fun size => aux_enum size
-/
#guard_msgs(info, drop warning) in
#derive_enum Value

end CommandElaboratorTest
