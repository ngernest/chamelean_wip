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
        let rec aux_arb (fuel : Nat) : Plausible.Gen Tree :=
          match fuel with
          | Nat.zero => Plausible.Gen.oneOfWithDefault (pure Tree.Leaf) [(pure Tree.Leaf)]
          | fuel' + 1 =>
            Plausible.Gen.frequency (pure Tree.Leaf)
              [(1, (pure Tree.Leaf)),
                (fuel' + 1,
                  (do
                    let a_0 ← Plausible.Arbitrary.arbitrary
                    let a_1 ← aux_arb fuel'
                    let a_2 ← aux_arb fuel'
                    return Tree.Node a_0 a_1 a_2))]
        fun fuel => aux_arb fuel
-/
#guard_msgs in
deriving instance Arbitrary for Tree

-- Test that we can successfully synthefuel instances of `Arbitrary` & `ArbitraryFueled`

/-- info: instArbitraryFueledTree -/
#guard_msgs in
#synth ArbitraryFueled Tree

/-- info: instArbitraryOfArbitraryFueled -/
#guard_msgs in
#synth Arbitrary Tree
