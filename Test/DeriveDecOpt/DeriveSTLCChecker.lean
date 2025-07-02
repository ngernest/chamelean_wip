import Plausible.New.DecOpt
import Plausible.New.DeriveChecker
import Test.DeriveDecOpt.DeriveBSTChecker
import Test.DeriveArbitrarySuchThat.NonLinearPatternsTest

open DecOpt

set_option guard_msgs.diff true

-- TODO: investigate why `τ'` and not `τ` is appearing as the head of the list in the final pattern-match

/--
info: Try this checker: instance : DecOpt (lookup Γ x τ) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (Γ_0 : List type) (x_0 : Nat) (τ_0 : type) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match Γ_0, x_0 with
            | τ :: Γ, 0 => Option.some Bool.true
            | _, _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match Γ_0, x_0 with
            | τ :: Γ, 0 => Option.some Bool.true
            | _, _ => Option.some Bool.false,
            fun _ =>
            match Γ_0, x_0 with
            | τ' :: Γ, Nat.succ n => DecOpt.andOptList [aux_dec initSize size' Γ n τ]
            | _, _ => Option.some Bool.false]
    fun size => aux_dec size size Γ x τ
-/
#guard_msgs(info, drop warning) in
#derive_checker (lookup Γ x τ)
