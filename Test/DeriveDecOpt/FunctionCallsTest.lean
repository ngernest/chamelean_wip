import Plausible.New.DecOpt
import Plausible.New.DeriveChecker
import Test.CommonDefinitions.FunctionCallInConclusion

open DecOpt

set_option guard_msgs.diff true

/--
info: Try this checker: instance : DecOpt (square_of n_1 m_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (n_1 : Nat) (m_1 : Nat) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            EnumeratorCombinators.enumeratingOpt
              (EnumSizedSuchThat.enumSizedST (fun m_1 => Eq m_1 (HMul.hMul n_1 n_1)) initSize)
              (fun m_1 => Option.some Bool.true) initSize]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            EnumeratorCombinators.enumeratingOpt
              (EnumSizedSuchThat.enumSizedST (fun m_1 => Eq m_1 (HMul.hMul n_1 n_1)) initSize)
              (fun m_1 => Option.some Bool.true) initSize,
            ]
    fun size => aux_dec size size n_1 m_1
-/
#guard_msgs(info, drop warning) in
#derive_scheduled_checker (square_of n m)
