import Plausible.Gen
import Plausible.New.Arbitrary
import Plausible.New.GeneratorCombinators
import Plausible.New.DeriveArbitrary
import Plausible.IR.Examples

open Arbitrary GeneratorCombinators

set_option guard_msgs.diff true

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
