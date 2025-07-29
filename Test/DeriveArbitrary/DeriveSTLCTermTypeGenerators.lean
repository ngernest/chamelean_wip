import Plausible.Arbitrary
import Plausible.DeriveArbitrary
import Plausible.Attr

open Plausible Gen

set_option guard_msgs.diff true

/-- Base types in the Simply-Typed Lambda Calculus (STLC)
    (either Nat or functions) -/
inductive type where
  | Nat : type
  | Fun : type → type → type
  deriving BEq, DecidableEq, Repr

/-- Terms in the STLC extended with naturals and addition -/
inductive term where
  | Const: Nat → term
  | Add: term → term → term
  | Var: Nat → term
  | App: term → term → term
  | Abs: type → term → term
  deriving BEq, Repr

-- Invoke deriving instance handler for the `Arbitrary` typeclass on `type` and `term`
set_option trace.plausible.deriving.arbitrary true in
/--
trace: [plausible.deriving.arbitrary] Derived generator: instance : Plausible.ArbitraryFueled type where
      arbitraryFueled :=
        let rec aux_arb (size : Nat) : Plausible.Gen type :=
          match size with
          | Nat.zero => Plausible.Gen.oneOfWithDefault (pure type.Nat) [(pure type.Nat)]
          | size' + 1 =>
            Plausible.Gen.frequency (pure type.Nat)
              [(1, (pure type.Nat)),
                (size' + 1,
                  (do
                    let a_0 ← aux_arb size'
                    let a_1 ← aux_arb size'
                    return type.Fun a_0 a_1))]
        fun size => aux_arb size
---
trace: [plausible.deriving.arbitrary] Derived generator: instance : Plausible.ArbitraryFueled term where
      arbitraryFueled :=
        let rec aux_arb (size : Nat) : Plausible.Gen term :=
          match size with
          | Nat.zero =>
            Plausible.Gen.oneOfWithDefault
              (do
                let a_0 ← Plausible.Arbitrary.arbitrary
                return term.Const a_0)
              [(do
                  let a_0 ← Plausible.Arbitrary.arbitrary
                  return term.Const a_0),
                (do
                  let a_0 ← Plausible.Arbitrary.arbitrary
                  return term.Var a_0)]
          | size' + 1 =>
            Plausible.Gen.frequency
              (do
                let a_0 ← Plausible.Arbitrary.arbitrary
                return term.Const a_0)
              [(1,
                  (do
                    let a_0 ← Plausible.Arbitrary.arbitrary
                    return term.Const a_0)),
                (1,
                  (do
                    let a_0 ← Plausible.Arbitrary.arbitrary
                    return term.Var a_0)),
                (size' + 1,
                  (do
                    let a_0 ← aux_arb size'
                    let a_1 ← aux_arb size'
                    return term.Add a_0 a_1)),
                (size' + 1,
                  (do
                    let a_0 ← aux_arb size'
                    let a_1 ← aux_arb size'
                    return term.App a_0 a_1)),
                (size' + 1,
                  (do
                    let a_0 ← Plausible.Arbitrary.arbitrary
                    let a_1 ← aux_arb size'
                    return term.Abs a_0 a_1))]
        fun size => aux_arb size
-/
#guard_msgs in
deriving instance Arbitrary for type, term

-- Test that we can successfully synthesize instances of `Arbitrary` & `ArbitraryFueled`
-- for both `type` & `term`

/-- info: instArbitraryFueledType -/
#guard_msgs in
#synth ArbitraryFueled type

/-- info: instArbitraryFueledTerm -/
#guard_msgs in
#synth ArbitraryFueled term

/-- info: instArbitraryOfArbitraryFueled -/
#guard_msgs in
#synth Arbitrary type

/-- info: instArbitraryOfArbitraryFueled -/
#guard_msgs in
#synth Arbitrary term
