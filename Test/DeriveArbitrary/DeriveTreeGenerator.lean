import Plausible.Arbitrary
import Plausible.DeriveArbitrary
import Plausible.Attr

open Plausible Gen

set_option guard_msgs.diff true

/-- A binary tree is either a single `Leaf`,
    or a `Node` containing a `Nat` with left & right sub-trees -/
inductive Tree where
| Leaf : Tree
| Node : Nat → Tree → Tree → Tree
deriving Repr

-- Invoke deriving instance handler for the `Arbitrary` typeclass on `type` and `term`
set_option trace.plausible.deriving.arbitrary true in
/--
trace: [plausible.deriving.arbitrary] Derived generator: instance : Plausible.ArbitraryFueled Tree where
      arbitraryFueled :=
        let rec aux_arb (size : Nat) : Plausible.Gen Tree :=
          match size with
          | Nat.zero => Plausible.Gen.oneOfWithDefault (pure Tree.Leaf) [(pure Tree.Leaf)]
          | size' + 1 =>
            Plausible.Gen.frequency (pure Tree.Leaf)
              [(1, (pure Tree.Leaf)),
                (size' + 1,
                  (do
                    let a_0 ← Plausible.Arbitrary.arbitrary
                    let a_1 ← aux_arb size'
                    let a_2 ← aux_arb size'
                    return Tree.Node a_0 a_1 a_2))]
        fun size => aux_arb size
-/
#guard_msgs in
deriving instance Arbitrary for Tree

-- Test that we can successfully synthesize instances of `Arbitrary` & `ArbitraryFueled`

/-- info: instArbitraryFueledTree -/
#guard_msgs in
#synth ArbitraryFueled Tree

/-- info: instArbitraryOfArbitraryFueled -/
#guard_msgs in
#synth Arbitrary Tree
