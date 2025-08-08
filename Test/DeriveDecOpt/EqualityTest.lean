import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.DeriveChecker

set_option guard_msgs.diff true

-- TODO: uncomment when checkers work for equality tests
/-
info: Try this generator: instance : ArbitrarySizedSuchThat Nat (fun m_1 => Eq m_1 n_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (n_1 : Nat) : OptionT Plausible.Gen Nat :=
      match size with
      | Nat.zero => OptionTGen.backtrack [(1, return n_1)]
      | Nat.succ size' => OptionTGen.backtrack [(1, return n_1), ]
    fun size => aux_arb size size n_1
-/
-- #guard_msgs(info, drop warning) in
-- #derive_checker (m = n)
