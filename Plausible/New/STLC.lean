import Plausible.IR.Examples
import Plausible.New.OptionTGen
import Plausible.New.DecOpt
import Plausible.New.GenSizedSuchThat
import Plausible.New.GeneratorCombinators

import Plausible.Gen
import Plausible.Sampleable

open Plausible
open OptionTGen
open GeneratorCombinators

-------------------------------------------------------------------------
-- Some example `DecOpt` checkers
--------------------------------------------------------------------------

/-- A handwritten checker which checks `lookup Γ x τ`
  (modelled after the automatically derived checker produced by QuickChick). -/
def checkLookup (Γ : List type) (x : Nat) (τ : type) : Nat → Option Bool :=
  let rec aux_arb (initSize : Nat) (size : Nat) (Γ : List type) (x : Nat) (τ : type) : Option Bool :=
    match size with
    | .zero =>
      checkerBacktrack [
        (fun _ =>
          match x with
          | .zero =>
            match Γ with
            | [] => some false
            | t :: _ =>
              match DecOpt.decOpt (τ = t) initSize with
              | some true => some true
              | some false => some false
              | none => none
          | .succ _ => some false),
        fun _ => none
      ]
    | .succ size' =>
      checkerBacktrack [
        (fun _ =>
          match Γ with
          | [] => some false
          | t :: _ =>
            match DecOpt.decOpt (τ = t) initSize with
            | some true => some true
            | some false => some false
            | none => none),
        (fun _ =>
          match x with
          | .zero => some false
          | .succ x' =>
            match Γ with
            | [] => some false
            | _ :: Γ' =>
              match aux_arb initSize size' Γ' x' τ with
              | some true => some true
              | some false => some false
              | none => none)
      ]
  fun size => aux_arb size size Γ x τ

/-- `lookup Γ x τ` is an instance of the `DecOpt` typeclass which describes
     partially decidable propositions -/
instance : DecOpt (lookup Γ x τ) where
  decOpt := checkLookup Γ x τ

/-- A handwritten checker which checks `typing Γ e τ`, ignoring the case for `App`
    (based on the auto-derived checker produced by QuickChick) -/
def checkTyping (Γ : List type) (e : term) (τ : type) : Nat → Option Bool :=
  let rec aux_arb (initSize : Nat) (size : Nat) (Γ : List type) (e : term) (τ : type) : Option Bool :=
    match size with
    | .zero =>
      checkerBacktrack [
        fun _ =>
          match e with
          | .Var x =>
            match DecOpt.decOpt (lookup Γ x τ) initSize with
            | some true => some true
            | some false => some false
            | none => none
          | _ => some false,
        fun _ =>
          match τ with
          | .Nat =>
            match e with
            | .Const _ => some true
            | _ => some false
          | .Fun _ _ => some false,
        fun _ => none
      ]
    | .succ size' =>
      checkerBacktrack [
        fun _ =>
          match e with
          | .Var x =>
            match DecOpt.decOpt (lookup Γ x τ) initSize with
            | some true => some true
            | some false => some false
            | none => none
          | _ => some false,
        fun _ =>
          match τ with
          | .Nat =>
            match e with
            | .Const _ => some true
            | _ => some false
          | .Fun _ _ => some false,
        fun _ =>
          match τ with
          | .Nat => some false
          | .Fun unkn_17_ τ2 =>
            match e with
            | .Abs τ1 e =>
              match DecOpt.decOpt (τ1 = unkn_17_) initSize with
              | some true => aux_arb initSize size' (τ1 :: Γ) e τ2
              | some false => some false
              | none => none
            | _ => none,
        -- TODO: handle App case
      ]
  fun size => aux_arb size size Γ e τ

/-- `typing Γ e τ` is an instance of the `DecOpt` typeclass which describes
     partially decidable propositions -/
instance : DecOpt (typing Γ e τ) where
  decOpt := checkTyping Γ e τ

-------------------------------------------------------------------------
-- Unconstrained generators
--------------------------------------------------------------------------

/-- A generator for STLC types -/
def genType : Nat → Gen type :=
  let rec arb_aux (size : Nat) : Gen type :=
    match size with
    | 0 => pure .Nat
    | .succ size' =>
        frequency (pure .Nat)
          [(1, thunkGen $ fun _ => pure .Nat),
          (.succ size',
            thunkGen $ fun _ => do
              let p0 ← arb_aux size'
              let p1 ← arb_aux size'
              pure (.Fun p0 p1))]
  fun n => arb_aux n

instance : Shrinkable type where
  shrink := fun ty =>
    match ty with
    | .Nat => []
    | .Fun τ1 τ2 => [τ1, τ2]

/-- `SampleableExt` instance for STLC types -/
instance : SampleableExt type :=
  SampleableExt.mkSelfContained do
    genType (← Gen.getSize)

-------------------------------------------------------------------------
-- Constrained generators
--------------------------------------------------------------------------

/-- Generator which produces `x : Nat` such that `lookup Γ x τ` holds -/
def gen_lookup (Γ : List type) (τ : type) : Nat → OptionT Plausible.Gen Nat :=
  let rec aux_arb (initSize : Nat) (size : Nat) (Γ_0 : List type) (τ_0 : type) : OptionT Plausible.Gen Nat :=
    match size with
    | Nat.zero =>
      OptionTGen.backtrack
        [(1,
            OptionTGen.thunkGen
              (fun _ =>
                match Γ_0 with
                | [] => OptionT.fail
                -- TODO: need to rename patterns
                | τ :: _ =>
                  match DecOpt.decOpt (τ_0 = τ) initSize with
                  | some true => pure 0
                  | _ => OptionT.fail)),
          (1, OptionTGen.thunkGen (fun _ => OptionT.fail))]
    | Nat.succ size' =>
      OptionTGen.backtrack
        [(1,
            OptionTGen.thunkGen
              (fun _ =>
                match Γ_0 with
                | [] => OptionT.fail
                | τ :: _ =>
                  match DecOpt.decOpt (τ_0 = τ) initSize with
                  | some true => pure 0
                  | _ => OptionT.fail)),
          (Nat.succ size',
            OptionTGen.thunkGen
              (fun _ =>
                match Γ_0 with
                | [] => OptionT.fail
                | _ :: Γ0 => do
                  let x ← aux_arb initSize size' Γ0 τ_0
                  return Nat.succ x))]
  fun size => aux_arb size size Γ τ

/-- `lookup Γ x τ` is an instance of the `GenSizedSuchThat` typeclass,
    which describes generators for values that satisfy a proposition -/
instance : GenSizedSuchThat Nat (fun x => lookup Γ x τ) where
  genSizedST := gen_lookup Γ τ

/-- Generator which produces well-typed terms `e` such that `typing Γ e τ` holds -/
def gen_typing (G_ : List type) (t_ : type) : Nat → OptionT Plausible.Gen term :=
  let rec aux_arb (initSize : Nat) (size : Nat) (G_0 : List type) (t_0 : type) : OptionT Plausible.Gen term :=
    match size with
    | Nat.zero =>
      OptionTGen.backtrack
        [(1,
            OptionTGen.thunkGen
              (fun _ =>
                match t_0 with
                | .Nat => do
                  let n ← SampleableExt.interpSample Nat
                  return term.Const n
                | .Fun _ _ => OptionT.fail)),
          (1,
            OptionTGen.thunkGen
              (fun _ => do
                let x ← GenSuchThat.genST (fun x => lookup G_0 x t_0)
                return term.Var x)),
          (1, OptionTGen.thunkGen (fun _ => OptionT.fail))]
    | Nat.succ size' =>
      OptionTGen.backtrack
        [(1,
            OptionTGen.thunkGen
              (fun _ =>
                match t_0 with
                | type.Nat => do
                  let n ← SampleableExt.interpSample Nat
                  return term.Const n
                | _ => OptionT.fail)),
          (Nat.succ size',
            OptionTGen.thunkGen
              (fun _ =>
                match t_0 with
                | type.Nat => do
                  let e1 ← aux_arb initSize size' G_0 type.Nat
                  let e2 ← aux_arb initSize size' G_0 type.Nat
                  return term.Add e1 e2
                | _ => OptionT.fail)),
          (Nat.succ size',
            OptionTGen.thunkGen
              (fun _ =>
                match t_0 with
                | type.Fun t1 t2 => do
                  let e ← aux_arb initSize size' (t1 :: G_0) t2
                  return term.Abs t1 e
                | _ => OptionT.fail)),
          (1,
            OptionTGen.thunkGen
              (fun _ => do
                let x ← GenSuchThat.genST (fun x => lookup G_0 x t_0)
                return term.Var x)),
          (Nat.succ size',
            OptionTGen.thunkGen
              (fun _ => do
                let t1 ← SampleableExt.interpSample type
                let e2 ← aux_arb initSize size' G_0 t1
                let e1 ← aux_arb initSize size' G_0 (type.Fun t1 t_0)
                return term.App (.Abs .Nat e1) e2))]
  fun size => aux_arb size size G_ t_

/-- `typing Γ e τ` is an instance of the `GenSizedSuchThat` typeclass,
    which describes generators for values that satisfy a proposition -/
instance : GenSizedSuchThat term (fun e => typing Γ e τ) where
  genSizedST := gen_typing Γ τ
