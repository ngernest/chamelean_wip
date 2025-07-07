import Plausible.New.DecOpt
import Plausible.New.DeriveChecker
import Plausible.New.EnumeratorCombinators
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
            | τ :: Γ_1, 0 => Option.some Bool.true
            | _, _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match Γ_0, x_0 with
            | τ :: Γ_1, 0 => Option.some Bool.true
            | _, _ => Option.some Bool.false,
            fun _ =>
            match Γ_0, x_0 with
            | τ' :: Γ_1, Nat.succ n => aux_dec initSize size' Γ_1 n τ
            | _, _ => Option.some Bool.false]
    fun size => aux_dec size size Γ x τ
-/
#guard_msgs(info, drop warning) in
#derive_checker (lookup Γ x τ)

-- Dummy `EnumSizedSuchThat` instance
-- TODO: implement metaprogramming infrastructure for deriving `EnumSizedSuchThat` instances
instance : EnumSizedSuchThat type (fun τ => typing Γ e τ) where
  enumSizedST := fun _ => OptionT.fail

/--
info: Try this checker: instance : DecOpt (typing Γ e τ) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (Γ_0 : List type) (e_0 : term) (τ_0 : type) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match e_0, τ_0 with
            | term.Const n, type.Nat => Option.some Bool.true
            | _, _ => Option.some Bool.false,
            fun _ =>
            match e_0 with
            | term.Var x => DecOpt.decOpt (lookup Γ x τ) initSize
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match e_0, τ_0 with
            | term.Const n, type.Nat => Option.some Bool.true
            | _, _ => Option.some Bool.false,
            fun _ =>
            match e_0, τ_0 with
            | term.Add e1 e2, type.Nat =>
              DecOpt.andOptList [aux_dec initSize size' Γ e1 type.Nat, aux_dec initSize size' Γ e2 type.Nat]
            | _, _ => Option.some Bool.false,
            fun _ =>
            match e_0, τ_0 with
            | term.Abs τ1 e_1, type.Fun τ1_0 τ2 => aux_dec initSize size' (τ1 :: Γ) e_1 τ2
            | _, _ => Option.some Bool.false,
            fun _ =>
            match e_0 with
            | term.Var x => DecOpt.decOpt (lookup Γ x τ) initSize
            | _ => Option.some Bool.false,
            fun _ =>
            match e_0 with
            | term.App (term.Abs type.Nat e1) e2 =>
              EnumeratorCombinators.enumeratingOpt (EnumSuchThat.enumST (fun τ1 => typing Γ e2 τ1))
                (fun τ1 => aux_dec initSize size' Γ e1 (type.Fun τ1 τ)) initSize
            | _ => Option.some Bool.false]
    fun size => aux_dec size size Γ e τ
-/
#guard_msgs(info, drop warning) in
#derive_checker (typing Γ e τ)
