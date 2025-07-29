import Plausible.Arbitrary
import Plausible.DeriveArbitrary
import Plausible.Attr

open Plausible Gen

set_option guard_msgs.diff true

/-- Dummy `structure` with named fields -/
structure Foo where
  stringField : String
  boolField : Bool
  natField : Nat

-- Test that we can successfully synthesize instances of `Arbitrary` & `ArbitraryFueled`
set_option trace.plausible.deriving.arbitrary true in
/--
trace: [plausible.deriving.arbitrary] Derived generator: instance : Plausible.ArbitraryFueled Foo where
      arbitraryFueled :=
        let rec aux_arb (size : Nat) : Plausible.Gen Foo :=
          match size with
          | Nat.zero =>
            Plausible.Gen.oneOfWithDefault
              (do
                let stringField_0 ← Plausible.Arbitrary.arbitrary
                let boolField_0 ← Plausible.Arbitrary.arbitrary
                let natField_0 ← Plausible.Arbitrary.arbitrary
                return Foo.mk stringField_0 boolField_0 natField_0)
              [(do
                  let stringField_0 ← Plausible.Arbitrary.arbitrary
                  let boolField_0 ← Plausible.Arbitrary.arbitrary
                  let natField_0 ← Plausible.Arbitrary.arbitrary
                  return Foo.mk stringField_0 boolField_0 natField_0)]
          | size' + 1 =>
            Plausible.Gen.frequency
              (do
                let stringField_0 ← Plausible.Arbitrary.arbitrary
                let boolField_0 ← Plausible.Arbitrary.arbitrary
                let natField_0 ← Plausible.Arbitrary.arbitrary
                return Foo.mk stringField_0 boolField_0 natField_0)
              [(1,
                  (do
                    let stringField_0 ← Plausible.Arbitrary.arbitrary
                    let boolField_0 ← Plausible.Arbitrary.arbitrary
                    let natField_0 ← Plausible.Arbitrary.arbitrary
                    return Foo.mk stringField_0 boolField_0 natField_0)),
                ]
        fun size => aux_arb size
-/
#guard_msgs in
deriving instance Arbitrary for Foo

/-- info: instArbitraryFueledFoo -/
#guard_msgs in
#synth ArbitraryFueled Foo

/-- info: instArbitraryOfArbitraryFueled -/
#guard_msgs in
#synth Arbitrary Foo
