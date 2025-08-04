import Plausible.Gen
import Plausible.New.OptionTGen
import Plausible.New.DecOpt
import Plausible.New.ArbitrarySizedSuchThat
import Plausible.New.DeriveArbitrarySuchThat

open ArbitrarySizedSuchThat OptionTGen

set_option guard_msgs.diff true

-- TODO: figure out why `τ_1_0` isn't occuring as the head of the list in the first two patern matches

-- TODO: investigate why `τ'` and not `τ` is appearing as the head of the list in the final pattern-match
-- (and why `τ` rather than `τ'` is used as a function argument on line 47)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat Nat (fun x => lookup Γ x τ) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (Γ_1 : List type) (τ_1 : type) : OptionT Plausible.Gen Nat :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              OptionTGen.thunkGen
                (fun _ =>
                  match Γ_1 with
                  | τ_1 :: Γ =>
                    match DecOpt.decOpt (τ_1 = τ_1_0) initSize with
                    | Option.some Bool.true => pure Nat.zero
                    | _ => OptionT.fail
                  | _ => OptionT.fail)),
            (1, OptionTGen.thunkGen (fun _ => OptionT.fail))]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              OptionTGen.thunkGen
                (fun _ =>
                  match Γ_1 with
                  | τ_1 :: Γ =>
                    match DecOpt.decOpt (τ_1 = τ_1_0) initSize with
                    | Option.some Bool.true => pure Nat.zero
                    | _ => OptionT.fail
                  | _ => OptionT.fail))]
    fun size => aux_arb size size Γ τ
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (x : Nat) => lookup Γ x τ)
