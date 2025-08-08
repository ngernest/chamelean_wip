import Plausible.Gen
import Plausible.Chamelean.Arbitrary
import Plausible.Chamelean.GeneratorCombinators
import Plausible.Chamelean.DeriveArbitrary
import Plausible.Chamelean.Examples.ExampleInductiveRelations

open Arbitrary GeneratorCombinators

set_option guard_msgs.diff true

-- Note: the `float` constructor has been removed for now since there is currently
-- no `Arbitrary` instance for floats
inductive Value where
  | none
  | bool (value : Bool)
  | int (value : Int)
  | string (value : String)
  | ellipsis
  | tensor (shape : List Nat) (dtype : String)
  deriving Repr, Arbitrary

-- Test that we can successfully synthesize instances of `Arbitrary` & `ArbitrarySized`

/-- info: instArbitrarySizedValue -/
#guard_msgs in
#synth ArbitrarySized Value

/-- info: instArbitraryOfArbitrarySized -/
#guard_msgs in
#synth Arbitrary Value

-- We test the command elaborator frontend in a separate namespace to
-- avoid overlapping typeclass instances for the same type
namespace CommandElaboratorTest

/--
info: Try this generator: instance : ArbitrarySized Value where
  arbitrarySized :=
    let rec aux_arb (size : Nat) : Plausible.Gen Value :=
      match size with
      | Nat.zero =>
        GeneratorCombinators.oneOfWithDefault (pure Value.none)
          [GeneratorCombinators.thunkGen (fun _ => pure Value.none),
            GeneratorCombinators.thunkGen
              (fun _ => do
                let value_0 ← Arbitrary.arbitrary
                return Value.bool value_0),
            GeneratorCombinators.thunkGen
              (fun _ => do
                let value_0 ← Arbitrary.arbitrary
                return Value.int value_0),
            GeneratorCombinators.thunkGen
              (fun _ => do
                let value_0 ← Arbitrary.arbitrary
                return Value.string value_0),
            GeneratorCombinators.thunkGen (fun _ => pure Value.ellipsis),
            GeneratorCombinators.thunkGen
              (fun _ => do
                let shape_0 ← Arbitrary.arbitrary
                let dtype_0 ← Arbitrary.arbitrary
                return Value.tensor shape_0 dtype_0)]
      | Nat.succ size' =>
        GeneratorCombinators.frequency (pure Value.none)
          [(1, GeneratorCombinators.thunkGen (fun _ => pure Value.none)),
            (1,
              GeneratorCombinators.thunkGen
                (fun _ => do
                  let value_0 ← Arbitrary.arbitrary
                  return Value.bool value_0)),
            (1,
              GeneratorCombinators.thunkGen
                (fun _ => do
                  let value_0 ← Arbitrary.arbitrary
                  return Value.int value_0)),
            (1,
              GeneratorCombinators.thunkGen
                (fun _ => do
                  let value_0 ← Arbitrary.arbitrary
                  return Value.string value_0)),
            (1, GeneratorCombinators.thunkGen (fun _ => pure Value.ellipsis)),
            (1,
              GeneratorCombinators.thunkGen
                (fun _ => do
                  let shape_0 ← Arbitrary.arbitrary
                  let dtype_0 ← Arbitrary.arbitrary
                  return Value.tensor shape_0 dtype_0)),
            ]
    fun size => aux_arb size
-/
#guard_msgs(info, drop warning) in
#derive_arbitrary Value

end CommandElaboratorTest
