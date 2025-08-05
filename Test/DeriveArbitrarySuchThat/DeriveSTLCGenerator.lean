import Plausible.Gen
import Plausible.New.OptionTGen
import Plausible.New.DecOpt
import Plausible.New.ArbitrarySizedSuchThat
import Plausible.GeneratingGoodGenerators.DeriveSubGenerator

open ArbitrarySizedSuchThat OptionTGen

set_option guard_msgs.diff true

/--
info: Try this generator: instance : ArbitrarySizedSuchThat Nat (fun x_1 => lookup Γ_1 x_1 τ_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (Γ_1 : List type) (τ_1 : type) : OptionT Plausible.Gen Nat :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              match Γ_1 with
              | List.cons τ Γ =>
                match DecOpt.decOpt (BEq.beq τ τ_1) initSize with
                | Option.some Bool.true => return Nat.zero
                | _ => OptionT.fail
              | _ => OptionT.fail)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              match Γ_1 with
              | List.cons τ Γ =>
                match DecOpt.decOpt (BEq.beq τ τ_1) initSize with
                | Option.some Bool.true => return Nat.zero
                | _ => OptionT.fail
              | _ => OptionT.fail),
            ]
    fun size => aux_arb size size Γ_1 τ_1
-/
#guard_msgs(info, drop warning) in
#derive_scheduled_generator (fun (x : Nat) => lookup Γ x τ)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat term (fun e_1 => typing G_1 e_1 t_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (G_1 : List type) (t_1 : type) : OptionT Plausible.Gen term :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              match t_1 with
              | type.Nat => do
                let n ← Arbitrary.arbitrary;
                return term.Const n
              | _ => OptionT.fail),
            (1, do
              let x ← ArbitrarySizedSuchThat.arbitrarySizedST (fun x => lookup G_1 x t_1) initSize;
              return term.Var x)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              match t_1 with
              | type.Nat => do
                let n ← Arbitrary.arbitrary;
                return term.Const n
              | _ => OptionT.fail),
            (1, do
              let x ← ArbitrarySizedSuchThat.arbitrarySizedST (fun x => lookup G_1 x t_1) initSize;
              return term.Var x),
            (Nat.succ size',
              match t_1 with
              | type.Nat => do
                let e1 ← aux_arb initSize size' G_1 (type.Nat);
                do
                  let e2 ← aux_arb initSize size' G_1 (type.Nat);
                  return term.Add e1 e2
              | _ => OptionT.fail),
            (Nat.succ size',
              match t_1 with
              | type.Fun τ1 τ2 => do
                let e ← aux_arb initSize size' (List.cons τ1 G_1) τ2;
                return term.Abs τ1 e
              | _ => OptionT.fail),
            (Nat.succ size', do
              let e2 ← Arbitrary.arbitrary;
              do
                let τ1 ← ArbitrarySizedSuchThat.arbitrarySizedST (fun τ1 => typing G_1 e2 τ1) initSize;
                do
                  let e1 ← aux_arb initSize size' G_1 (type.Fun τ1 t_1);
                  return term.App e1 e2)]
    fun size => aux_arb size size G_1 t_1
-/
#guard_msgs(info, drop warning) in
#derive_scheduled_generator (fun (e : term) => typing G e t)
