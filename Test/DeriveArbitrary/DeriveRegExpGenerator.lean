import Plausible.Attr
import Plausible.Arbitrary
import Plausible.DeriveArbitrary

open Plausible Gen

set_option guard_msgs.diff true

/-- An inductive datatype representing regular expressions (where "characters" are `Nat`s).
   Slightly modified from Software Foundations
   See https://softwarefoundations.cis.upenn.edu/lf-current/IndProp.html
   and search for "Case Study: Regular Expressions".
   The `RegExp`s below are non-polymorphic in the character type. -/
inductive RegExp : Type where
  | EmptySet : RegExp
  | EmptyStr : RegExp
  | Char : Nat → RegExp -- using Nat instead of Char
  | App : RegExp → RegExp → RegExp
  | Union : RegExp → RegExp → RegExp
  | Star : RegExp → RegExp

set_option trace.plausible.deriving.arbitrary true in
/--
trace: [plausible.deriving.arbitrary] Derived generator: instance : Plausible.ArbitraryFueled RegExp where
      arbitraryFueled :=
        let rec aux_arb (fuel : Nat) : Plausible.Gen RegExp :=
          match fuel with
          | Nat.zero =>
            Plausible.Gen.oneOfWithDefault (pure RegExp.EmptySet)
              [(pure RegExp.EmptySet), (pure RegExp.EmptyStr),
                (do
                  let a_0 ← Plausible.Arbitrary.arbitrary
                  return RegExp.Char a_0)]
          | fuel' + 1 =>
            Plausible.Gen.frequency (pure RegExp.EmptySet)
              [(1, (pure RegExp.EmptySet)), (1, (pure RegExp.EmptyStr)),
                (1,
                  (do
                    let a_0 ← Plausible.Arbitrary.arbitrary
                    return RegExp.Char a_0)),
                (fuel' + 1,
                  (do
                    let a_0 ← aux_arb fuel'
                    let a_1 ← aux_arb fuel'
                    return RegExp.App a_0 a_1)),
                (fuel' + 1,
                  (do
                    let a_0 ← aux_arb fuel'
                    let a_1 ← aux_arb fuel'
                    return RegExp.Union a_0 a_1)),
                (fuel' + 1,
                  (do
                    let a_0 ← aux_arb fuel'
                    return RegExp.Star a_0))]
        fun fuel => aux_arb fuel
-/
#guard_msgs in
deriving instance Arbitrary for RegExp

-- Test that we can successfully synthefuel instances of `Arbitrary` & `ArbitraryFueled`

/-- info: instArbitraryFueledRegExp -/
#guard_msgs in
#synth ArbitraryFueled RegExp

/-- info: instArbitraryOfArbitraryFueled -/
#guard_msgs in
#synth Arbitrary RegExp
