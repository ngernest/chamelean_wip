import Plausible.New.DecOpt
import Plausible.New.Enumerators
import Plausible.New.DeriveEnumSuchThat
import Plausible.New.EnumeratorCombinators


set_option guard_msgs.diff true

-- TODO: investigate why `τ'` and not `τ` is appearing as the head of the list in the final pattern-match

/--
info: Try this enumerator: instance : EnumSizedSuchThat Nat (fun x => lookup Γ x τ) where
  enumSizedST :=
    let rec aux_enum (initSize : Nat) (size : Nat) (Γ_1 : List type) (τ_1 : type) : OptionT Enumerator Nat :=
      match size with
      | Nat.zero =>
        EnumeratorCombinators.enumerate
          [match Γ_1 with
            | τ_1 :: Γ =>
              match DecOpt.decOpt (τ_1 = τ_1_0) initSize with
              | Option.some Bool.true => pure 0
              | _ => OptionT.fail
            | _ => OptionT.fail,
            OptionT.fail]
      | Nat.succ size' =>
        EnumeratorCombinators.enumerate
          [match Γ_1 with
            | τ_1 :: Γ =>
              match DecOpt.decOpt (τ_1 = τ_1_0) initSize with
              | Option.some Bool.true => pure 0
              | _ => OptionT.fail
            | _ => OptionT.fail,
            match Γ_1 with
            | τ' :: Γ => do
              let n ← aux_enum initSize size' Γ τ_1
              return Nat.succ n
            | _ => OptionT.fail]
    fun size => aux_enum size size Γ τ
-/
#guard_msgs(info, drop warning) in
#derive_enumerator (fun (x : Nat) => lookup Γ x τ)
