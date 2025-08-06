import Plausible.New.DecOpt
import Plausible.New.DeriveChecker
import Test.CommonDefinitions.FunctionCallInConclusion

open DecOpt

set_option guard_msgs.diff true

/--
info: Try this checker: instance : DecOpt (square_of n m) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (n_1 : Nat) (m_1 : Nat) : Option Bool :=
      match size with
      | Nat.zero => DecOpt.checkerBacktrack [fun _ => DecOpt.decOpt (@Eq Nat m_1 (n_1 * n_1)) initSize]
      | Nat.succ size' => DecOpt.checkerBacktrack [fun _ => DecOpt.decOpt (@Eq Nat m_1 (n_1 * n_1)) initSize]
    fun size => aux_dec size size n m
-/
#guard_msgs(info, drop warning) in
#derive_checker (square_of n m)
