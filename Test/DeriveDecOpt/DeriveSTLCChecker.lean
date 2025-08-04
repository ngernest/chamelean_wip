import Plausible.New.DecOpt
import Plausible.New.DeriveChecker
import Plausible.New.EnumeratorCombinators
import Test.DeriveDecOpt.DeriveBSTChecker

open DecOpt

set_option guard_msgs.diff true

/--
info: Try this checker: instance : DecOpt (lookup Γ x τ) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (Γ_1 : List type) (x_1 : Nat) (τ_1 : type) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match Γ_1, x_1 with
            | τ_1 :: Γ, Nat.zero => Option.some Bool.true
            | _, _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match Γ_1, x_1 with
            | τ_1 :: Γ, Nat.zero => Option.some Bool.true
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
    let rec aux_dec (initSize : Nat) (size : Nat) (Γ_1 : List type) (e_1 : term) (τ_1 : type) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match e_1, τ_1 with
            | term.Const n, type.Nat => Option.some Bool.true
            | _, _ => Option.some Bool.false,
            fun _ =>
            match e_1 with
            | term.Var x => DecOpt.decOpt (lookup Γ_1 x τ_1) initSize
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match e_1, τ_1 with
            | term.Const n, type.Nat => Option.some Bool.true
            | _, _ => Option.some Bool.false,
            fun _ =>
            match e_1, τ_1 with
            | term.Add e1 e2, type.Nat =>
              DecOpt.andOptList [aux_dec initSize size' Γ_1 e1 type.Nat, aux_dec initSize size' Γ_1 e2 type.Nat]
            | _, _ => Option.some Bool.false,
            fun _ =>
            match e_1, τ_1 with
            | term.Abs τ1 e, type.Fun τ1_0 τ2 => aux_dec initSize size' (τ1 :: Γ_1) e τ2
            | _, _ => Option.some Bool.false,
            fun _ =>
            match e_1 with
            | term.Var x => DecOpt.decOpt (lookup Γ_1 x τ_1) initSize
            | _ => Option.some Bool.false,
            fun _ =>
            match e_1 with
            | term.App e1 e2 =>
              EnumeratorCombinators.enumeratingOpt (EnumSuchThat.enumST (fun τ1 => typing Γ_1 e2 τ1))
                (fun τ1 => aux_dec initSize size' Γ_1 e1 (type.Fun τ1 τ_1)) initSize
            | _ => Option.some Bool.false]
    fun size => aux_dec size size Γ e τ
-/
#guard_msgs(info, drop warning) in
#derive_checker (typing Γ e τ)
