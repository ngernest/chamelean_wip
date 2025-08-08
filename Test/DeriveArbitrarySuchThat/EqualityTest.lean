import Plausible.Chamelean.Arbitrary
import Plausible.Chamelean.ArbitrarySizedSuchThat
import Plausible.Chamelean.DeriveConstrainedProducer

set_option guard_msgs.diff true

-- Trivial generator which generates all values `m` that are equal to `n`

/--
info: Try this generator: instance : ArbitrarySizedSuchThat Nat (fun m_1 => Eq m_1 n_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (n_1 : Nat) : OptionT Plausible.Gen Nat :=
      match size with
      | Nat.zero => OptionTGen.backtrack [(1, return n_1)]
      | Nat.succ size' => OptionTGen.backtrack [(1, return n_1), ]
    fun size => aux_arb size size n_1
-/
#guard_msgs(info) in
#derive_generator (fun (m : Nat) => m = n)
