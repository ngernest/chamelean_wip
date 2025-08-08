import Plausible.New.DecOpt
import Plausible.New.DeriveChecker
import Plausible.New.EnumeratorCombinators
import Test.DeriveDecOpt.DeriveBSTChecker
import Test.DeriveEnumSuchThat.DeriveSTLCEnumerator

open DecOpt

set_option guard_msgs.diff true

/--
info: Try this checker: instance : DecOpt (lookup Γ_1 x_1 τ_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (Γ_1 : List type) (x_1 : Nat) (τ_1 : type) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match x_1 with
            | Nat.zero =>
              match Γ_1 with
              | List.cons τ Γ => DecOpt.andOptList [DecOpt.decOpt (BEq.beq τ τ_1) initSize, Option.some Bool.true]
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match x_1 with
            | Nat.zero =>
              match Γ_1 with
              | List.cons τ Γ => DecOpt.andOptList [DecOpt.decOpt (BEq.beq τ τ_1) initSize, Option.some Bool.true]
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match x_1 with
            | Nat.succ n =>
              match Γ_1 with
              | List.cons τ' Γ => DecOpt.andOptList [aux_dec initSize size' Γ n τ_1, Option.some Bool.true]
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false]
    fun size => aux_dec size size Γ_1 x_1 τ_1
-/
#guard_msgs(info, drop warning) in
#derive_scheduled_checker (lookup Γ x τ)

/--
info: Try this checker: instance : DecOpt (typing Γ_1 e_1 τ_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (Γ_1 : List type) (e_1 : term) (τ_1 : type) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match τ_1 with
            | type.Nat =>
              match e_1 with
              | term.Const n => Option.some Bool.true
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match e_1 with
            | term.Var x => DecOpt.andOptList [DecOpt.decOpt (lookup Γ_1 x τ_1) initSize, Option.some Bool.true]
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match τ_1 with
            | type.Nat =>
              match e_1 with
              | term.Const n => Option.some Bool.true
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match e_1 with
            | term.Var x => DecOpt.andOptList [DecOpt.decOpt (lookup Γ_1 x τ_1) initSize, Option.some Bool.true]
            | _ => Option.some Bool.false,
            fun _ =>
            match τ_1 with
            | type.Nat =>
              match e_1 with
              | term.Add e1 e2 =>
                DecOpt.andOptList
                  [aux_dec initSize size' Γ_1 e1 (type.Nat),
                    DecOpt.andOptList [aux_dec initSize size' Γ_1 e2 (type.Nat), Option.some Bool.true]]
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match τ_1 with
            | type.Fun u_3 τ2 =>
              match e_1 with
              | term.Abs τ1 e =>
                DecOpt.andOptList
                  [DecOpt.decOpt (BEq.beq u_3 τ1) initSize,
                    DecOpt.andOptList [aux_dec initSize size' (List.cons τ1 Γ_1) e τ2, Option.some Bool.true]]
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match e_1 with
            | term.App e1 e2 =>
              EnumeratorCombinators.enumeratingOpt (aux_dec initSize size' Γ_1 e2 τ1)
                (fun τ1 => DecOpt.andOptList [aux_dec initSize size' Γ_1 e1 (type.Fun τ1 τ_1), Option.some Bool.true])
                initSize
            | _ => Option.some Bool.false]
    fun size => aux_dec size size Γ_1 e_1 τ_1
-/
#guard_msgs(info, drop warning) in
#derive_scheduled_checker (typing Γ e τ)
