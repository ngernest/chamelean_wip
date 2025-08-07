import Plausible.New.DecOpt
import Plausible.New.Enumerators
import Plausible.New.DeriveEnumSuchThat
import Plausible.New.EnumeratorCombinators


set_option guard_msgs.diff true

-- TODO: re-enable these failing tests after checker/enumerator deriver has been updated to use schedules

/-
info: Try this enumerator: instance : EnumSizedSuchThat Nat (fun x => lookup Γ x τ) where
  enumSizedST :=
    let rec aux_enum (initSize : Nat) (size : Nat) (Γ_1 : List type) (τ_1 : type) : OptionT Enumerator Nat :=
      match size with
      | Nat.zero =>
        EnumeratorCombinators.enumerate
          [match Γ_1 with
            | τ_1 :: Γ =>
              match DecOpt.decOpt (τ_1 = τ_1_0) initSize with
              | Option.some Bool.true => pure Nat.zero
              | _ => OptionT.fail
            | _ => OptionT.fail,
            OptionT.fail]
      | Nat.succ size' =>
        EnumeratorCombinators.enumerate
          [match Γ_1 with
            | τ_1 :: Γ =>
              match DecOpt.decOpt (τ_1 = τ_1_0) initSize with
              | Option.some Bool.true => pure Nat.zero
              | _ => OptionT.fail
            | _ => OptionT.fail]
    fun size => aux_enum size size Γ τ
-/
-- #guard_msgs(info, drop warning) in
-- #derive_enumerator (fun (x : Nat) => lookup Γ x τ)
