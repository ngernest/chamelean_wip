import Plausible.Gen
import Plausible.Arbitrary
import Plausible.Gen
import Plausible.DeriveArbitrary

open Plausible Gen

set_option guard_msgs.diff true

/-- Binary operators for the NKI language,
    adapted from https://github.com/leanprover/KLR/blob/main/KLR/NKI/Basic.lean -/
inductive BinOp where
  -- logical
  | land | lor
  -- comparison
  | eq | ne | lt | le | gt | ge
  -- arithmetic
  | add | sub | mul | div | mod | pow | floor
  -- bitwise
  | lshift | rshift | or | xor | and
  deriving Repr, Arbitrary

-- Test that we can successfully synthesize instances of `Arbitrary` & `ArbitrarySized`

/-- info: instArbitrarySizedBinOp -/
#guard_msgs in
#synth ArbitrarySized BinOp

/-- info: instArbitraryOfArbitrarySized -/
#guard_msgs in
#synth Arbitrary BinOp

-- We test the command elaborator frontend in a separate namespace to
-- avoid overlapping typeclass instances for the same type
namespace CommandElaboratorTest

/--
info: Try this generator: instance : Plausible.ArbitrarySized BinOp where
  arbitrarySized :=
    let rec aux_arb (size : Nat) : Plausible.Gen BinOp :=
      match size with
      | Nat.zero =>
        Plausible.Gen.oneOfWithDefault (pure BinOp.land)
          [(pure BinOp.land), (pure BinOp.lor), (pure BinOp.eq), (pure BinOp.ne), (pure BinOp.lt), (pure BinOp.le),
            (pure BinOp.gt), (pure BinOp.ge), (pure BinOp.add), (pure BinOp.sub), (pure BinOp.mul), (pure BinOp.div),
            (pure BinOp.mod), (pure BinOp.pow), (pure BinOp.floor), (pure BinOp.lshift), (pure BinOp.rshift),
            (pure BinOp.or), (pure BinOp.xor), (pure BinOp.and)]
      | Nat.succ size' =>
        Plausible.Gen.frequency (pure BinOp.land)
          [(1, (pure BinOp.land)), (1, (pure BinOp.lor)), (1, (pure BinOp.eq)), (1, (pure BinOp.ne)),
            (1, (pure BinOp.lt)), (1, (pure BinOp.le)), (1, (pure BinOp.gt)), (1, (pure BinOp.ge)),
            (1, (pure BinOp.add)), (1, (pure BinOp.sub)), (1, (pure BinOp.mul)), (1, (pure BinOp.div)),
            (1, (pure BinOp.mod)), (1, (pure BinOp.pow)), (1, (pure BinOp.floor)), (1, (pure BinOp.lshift)),
            (1, (pure BinOp.rshift)), (1, (pure BinOp.or)), (1, (pure BinOp.xor)), (1, (pure BinOp.and)), ]
    fun size => aux_arb size
-/
#guard_msgs(info, drop warning) in
#derive_arbitrary BinOp

end CommandElaboratorTest
