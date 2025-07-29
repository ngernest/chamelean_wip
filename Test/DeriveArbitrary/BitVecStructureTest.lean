import Plausible.Arbitrary
import Plausible.DeriveArbitrary
import Plausible.Attr

open Plausible Gen

set_option guard_msgs.diff true

/-- Dummy `inductive` where a constructor has a dependently-typed argument (`BitVec n`)
    whose index does not appear in the overall type (`DummyInductive`) -/
inductive DummyInductive where
  | FromBitVec : ∀ (n : Nat), BitVec n → String → DummyInductive

set_option trace.plausible.deriving.arbitrary true in
/--
trace: [plausible.deriving.arbitrary] Derived generator: instance : Plausible.ArbitraryFueled DummyInductive where
      arbitraryFueled :=
        let rec aux_arb (fuel : Nat) : Plausible.Gen DummyInductive :=
          match fuel with
          | Nat.zero =>
            Plausible.Gen.oneOfWithDefault
              (do
                let n_0 ← Plausible.Arbitrary.arbitrary
                let a_0 ← Plausible.Arbitrary.arbitrary
                let a_1 ← Plausible.Arbitrary.arbitrary
                return DummyInductive.FromBitVec n_0 a_0 a_1)
              [(do
                  let n_0 ← Plausible.Arbitrary.arbitrary
                  let a_0 ← Plausible.Arbitrary.arbitrary
                  let a_1 ← Plausible.Arbitrary.arbitrary
                  return DummyInductive.FromBitVec n_0 a_0 a_1)]
          | fuel' + 1 =>
            Plausible.Gen.frequency
              (do
                let n_0 ← Plausible.Arbitrary.arbitrary
                let a_0 ← Plausible.Arbitrary.arbitrary
                let a_1 ← Plausible.Arbitrary.arbitrary
                return DummyInductive.FromBitVec n_0 a_0 a_1)
              [(1,
                  (do
                    let n_0 ← Plausible.Arbitrary.arbitrary
                    let a_0 ← Plausible.Arbitrary.arbitrary
                    let a_1 ← Plausible.Arbitrary.arbitrary
                    return DummyInductive.FromBitVec n_0 a_0 a_1)),
                ]
        fun fuel => aux_arb fuel
-/
#guard_msgs in
deriving instance Arbitrary for DummyInductive

-- Test that we can successfully synthefuel instances of `Arbitrary` & `ArbitraryFueled`

/-- info: instArbitraryFueledDummyInductive -/
#guard_msgs in
#synth ArbitraryFueled DummyInductive

/-- info: instArbitraryOfArbitraryFueled -/
#guard_msgs in
#synth Arbitrary DummyInductive
