import Plausible.Gen
import Plausible.New.Arbitrary
import Plausible.New.GeneratorCombinators
import Plausible.New.DeriveArbitrary
import Plausible.New.Examples.ExampleInductiveRelations

open Arbitrary GeneratorCombinators

set_option guard_msgs.diff true

-- Invoke deriving instance handler for the `Arbitrary` typeclass on `type` and `term`
deriving instance Arbitrary for type, term

-- Test that we can successfully synthesize instances of `Arbitrary` & `ArbitrarySized`
-- for both `type` & `term`

/-- info: instArbitrarySizedType_test -/
#guard_msgs in
#synth ArbitrarySized type

/-- info: instArbitrarySizedTerm_test -/
#guard_msgs in
#synth ArbitrarySized term

/-- info: instArbitraryOfArbitrarySized -/
#guard_msgs in
#synth Arbitrary type

/-- info: instArbitraryOfArbitrarySized -/
#guard_msgs in
#synth Arbitrary term

-- We test the command elaborator frontend in a separate namespace to
-- avoid overlapping typeclass instances for the same type
namespace CommandElaboratorTest

/--
info: Try this generator: instance : ArbitrarySized type where
  arbitrarySized :=
    let rec aux_arb (size : Nat) : Plausible.Gen type :=
      match size with
      | Nat.zero =>
        GeneratorCombinators.oneOfWithDefault (pure type.Nat) [GeneratorCombinators.thunkGen (fun _ => pure type.Nat)]
      | Nat.succ size' =>
        GeneratorCombinators.frequency (pure type.Nat)
          [(1, GeneratorCombinators.thunkGen (fun _ => pure type.Nat)),
            (Nat.succ size',
              GeneratorCombinators.thunkGen
                (fun _ => do
                  let a_0 ← aux_arb size'
                  let a_1 ← aux_arb size'
                  return type.Fun a_0 a_1))]
    fun size => aux_arb size
-/
#guard_msgs(info, drop warning) in
#derive_arbitrary type

/--
info: Try this generator: instance : ArbitrarySized term where
  arbitrarySized :=
    let rec aux_arb (size : Nat) : Plausible.Gen term :=
      match size with
      | Nat.zero =>
        GeneratorCombinators.oneOfWithDefault
          (do
            let a_0 ← Arbitrary.arbitrary
            return term.Const a_0)
          [GeneratorCombinators.thunkGen
              (fun _ => do
                let a_0 ← Arbitrary.arbitrary
                return term.Const a_0),
            GeneratorCombinators.thunkGen
              (fun _ => do
                let a_0 ← Arbitrary.arbitrary
                return term.Var a_0)]
      | Nat.succ size' =>
        GeneratorCombinators.frequency
          (do
            let a_0 ← Arbitrary.arbitrary
            return term.Const a_0)
          [(1,
              GeneratorCombinators.thunkGen
                (fun _ => do
                  let a_0 ← Arbitrary.arbitrary
                  return term.Const a_0)),
            (1,
              GeneratorCombinators.thunkGen
                (fun _ => do
                  let a_0 ← Arbitrary.arbitrary
                  return term.Var a_0)),
            (Nat.succ size',
              GeneratorCombinators.thunkGen
                (fun _ => do
                  let a_0 ← aux_arb size'
                  let a_1 ← aux_arb size'
                  return term.Add a_0 a_1)),
            (Nat.succ size',
              GeneratorCombinators.thunkGen
                (fun _ => do
                  let a_0 ← aux_arb size'
                  let a_1 ← aux_arb size'
                  return term.App a_0 a_1)),
            (Nat.succ size',
              GeneratorCombinators.thunkGen
                (fun _ => do
                  let a_0 ← Arbitrary.arbitrary
                  let a_1 ← aux_arb size'
                  return term.Abs a_0 a_1))]
    fun size => aux_arb size
-/
#guard_msgs(info, drop warning) in
#derive_arbitrary term

end CommandElaboratorTest
