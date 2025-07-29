import Plausible.Arbitrary
import Plausible.DeriveArbitrary
import Plausible.Attr

open Plausible Gen

set_option guard_msgs.diff true

/-- A datatype representing values in the NKI language, adapted from
    https://github.com/leanprover/KLR/blob/main/KLR/NKI/Basic.lean -/
inductive Value where
  | none
  | bool (value : Bool)
  | int (value : Int)
  | string (value : String)
  | ellipsis
  | tensor (shape : List Nat) (dtype : String)

set_option trace.plausible.deriving.arbitrary true in
/--
trace: [plausible.deriving.arbitrary] Derived generator: instance : Plausible.ArbitrarySized Value where
      arbitrarySized :=
        let rec aux_arb (size : Nat) : Plausible.Gen Value :=
          match size with
          | Nat.zero =>
            Plausible.Gen.oneOfWithDefault (pure Value.none)
              [(pure Value.none),
                (do
                  let value_0 ← Plausible.Arbitrary.arbitrary
                  return Value.bool value_0),
                (do
                  let value_0 ← Plausible.Arbitrary.arbitrary
                  return Value.int value_0),
                (do
                  let value_0 ← Plausible.Arbitrary.arbitrary
                  return Value.string value_0),
                (pure Value.ellipsis),
                (do
                  let shape_0 ← Plausible.Arbitrary.arbitrary
                  let dtype_0 ← Plausible.Arbitrary.arbitrary
                  return Value.tensor shape_0 dtype_0)]
          | Nat.succ size' =>
            Plausible.Gen.frequency (pure Value.none)
              [(1, (pure Value.none)),
                (1,
                  (do
                    let value_0 ← Plausible.Arbitrary.arbitrary
                    return Value.bool value_0)),
                (1,
                  (do
                    let value_0 ← Plausible.Arbitrary.arbitrary
                    return Value.int value_0)),
                (1,
                  (do
                    let value_0 ← Plausible.Arbitrary.arbitrary
                    return Value.string value_0)),
                (1, (pure Value.ellipsis)),
                (1,
                  (do
                    let shape_0 ← Plausible.Arbitrary.arbitrary
                    let dtype_0 ← Plausible.Arbitrary.arbitrary
                    return Value.tensor shape_0 dtype_0)),
                ]
        fun size => aux_arb size
-/
#guard_msgs in
deriving instance Arbitrary for Value

-- Test that we can successfully synthesize instances of `Arbitrary` & `ArbitrarySized`

/-- info: instArbitrarySizedValue -/
#guard_msgs in
#synth ArbitrarySized Value

/-- info: instArbitraryOfArbitrarySized -/
#guard_msgs in
#synth Arbitrary Value
