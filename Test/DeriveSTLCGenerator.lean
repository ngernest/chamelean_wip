import Plausible.Gen
import Plausible.New.OptionTGen
import Plausible.New.DecOpt
import Plausible.New.ArbitrarySizedSuchThat
import Plausible.New.DeriveGenerator

open ArbitrarySizedSuchThat OptionTGen

set_option guard_msgs.diff true

/--
info: Try this generator: instance : ArbitrarySizedSuchThat Nat (fun x => lookup Γ x τ) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (Γ_0 : List type) (τ_0 : type) : OptionT Plausible.Gen Nat :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              OptionTGen.thunkGen
                (fun _ =>
                  match Γ_0 with
                  | τ :: Γ =>
                    match DecOpt.decOpt (τ = τ_0) initSize with
                    | Option.some Bool.true => pure 0
                    | _ => OptionT.fail
                  | _ => OptionT.fail)),
            (1, OptionTGen.thunkGen (fun _ => OptionT.fail))]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              OptionTGen.thunkGen
                (fun _ =>
                  match Γ_0 with
                  | τ :: Γ =>
                    match DecOpt.decOpt (τ = τ_0) initSize with
                    | Option.some Bool.true => pure 0
                    | _ => OptionT.fail
                  | _ => OptionT.fail)),
            (Nat.succ size',
              OptionTGen.thunkGen
                (fun _ =>
                  match Γ_0 with
                  | τ' :: Γ => do
                    let n ← aux_arb initSize size' Γ τ
                    return Nat.succ n
                  | _ => OptionT.fail))]
    fun size => aux_arb size size Γ τ
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (x : Nat) => lookup Γ x τ)
