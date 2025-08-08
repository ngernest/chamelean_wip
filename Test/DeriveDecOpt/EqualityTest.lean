import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.DeriveChecker

set_option guard_msgs.diff true

-- Derived checker for equality between two `Nat`s

/--
info: Try this checker: instance : DecOpt ((@Eq Nat) m_1 n_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (m_1 : Nat) (n_1 : Nat) : Option Bool :=
      match size with
      | Nat.zero => DecOpt.checkerBacktrack [fun _ => DecOpt.decOpt (BEq.beq m_1 n_1) initSize]
      | Nat.succ size' => DecOpt.checkerBacktrack [fun _ => DecOpt.decOpt (BEq.beq m_1 n_1) initSize, ]
    fun size => aux_dec size size m_1 n_1
-/
#guard_msgs(info, drop warning) in
#derive_checker (m = n)
