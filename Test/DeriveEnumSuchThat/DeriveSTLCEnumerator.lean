import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.Enumerators
import Plausible.Chamelean.DeriveConstrainedProducer
import Plausible.Chamelean.EnumeratorCombinators


set_option guard_msgs.diff true

/--
info: Try this enumerator: instance : EnumSizedSuchThat Nat (fun x_1 => lookup Γ_1 x_1 τ_1) where
  enumSizedST :=
    let rec aux_enum (initSize : Nat) (size : Nat) (Γ_1 : List type) (τ_1 : type) : OptionT Enumerator Nat :=
      match size with
      | Nat.zero =>
        EnumeratorCombinators.enumerate
          [match Γ_1 with
            | List.cons τ Γ =>
              match DecOpt.decOpt (BEq.beq τ τ_1) initSize with
              | Option.some Bool.true => return Nat.zero
              | _ => OptionT.fail
            | _ => OptionT.fail]
      | Nat.succ size' =>
        EnumeratorCombinators.enumerate
          [match Γ_1 with
            | List.cons τ Γ =>
              match DecOpt.decOpt (BEq.beq τ τ_1) initSize with
              | Option.some Bool.true => return Nat.zero
              | _ => OptionT.fail
            | _ => OptionT.fail,
            match Γ_1 with
            | List.cons τ' Γ => do
              let n ← aux_enum initSize size' Γ τ_1;
              return Nat.succ n
            | _ => OptionT.fail]
    fun size => aux_enum size size Γ_1 τ_1
-/
#guard_msgs(info, drop warning) in
#derive_enumerator (fun (x : Nat) => lookup Γ x τ)
