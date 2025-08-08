import Plausible.Gen
import Plausible.New.Arbitrary
import Plausible.New.GeneratorCombinators
import Plausible.New.DeriveArbitrary
import Plausible.New.Examples.ExampleInductiveRelations

open Arbitrary GeneratorCombinators

set_option guard_msgs.diff true

-- Invoke deriving instance handler for the `Arbitrary` typeclass on `type` and `term`
deriving instance Arbitrary for Tree

-- Test that we can successfully synthesize instances of `Arbitrary` & `ArbitrarySized`

/-- info: instArbitrarySizedTree_test -/
#guard_msgs in
#synth ArbitrarySized Tree

/-- info: instArbitraryOfArbitrarySized -/
#guard_msgs in
#synth Arbitrary Tree

-- We test the command elaborator frontend in a separate namespace to
-- avoid overlapping typeclass instances for the same type
namespace CommandElaboratorTest

/--
info: Try this generator: instance : ArbitrarySized Tree where
  arbitrarySized :=
    let rec aux_arb (size : Nat) : Plausible.Gen Tree :=
      match size with
      | Nat.zero =>
        GeneratorCombinators.oneOfWithDefault (pure Tree.Leaf) [GeneratorCombinators.thunkGen (fun _ => pure Tree.Leaf)]
      | Nat.succ size' =>
        GeneratorCombinators.frequency (pure Tree.Leaf)
          [(1, GeneratorCombinators.thunkGen (fun _ => pure Tree.Leaf)),
            (Nat.succ size',
              GeneratorCombinators.thunkGen
                (fun _ => do
                  let a_0 ← Arbitrary.arbitrary
                  let a_1 ← aux_arb size'
                  let a_2 ← aux_arb size'
                  return Tree.Node a_0 a_1 a_2))]
    fun size => aux_arb size
-/
#guard_msgs(info, drop warning) in
#derive_arbitrary Tree

end CommandElaboratorTest
