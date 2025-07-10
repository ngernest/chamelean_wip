import Plausible.IR.Examples
import Plausible.New.OptionTGen
import Plausible.New.DecOpt
import Plausible.New.ArbitrarySizedSuchThat
import Plausible.New.GeneratorCombinators
import Plausible.New.Enumerators
import Plausible.New.EnumeratorCombinators

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
      DecOpt.checkerBacktrack [
        (fun _ =>
          match x with
          | .zero =>
            match Γ with
            | [] => some false
            | t :: _ => DecOpt.andOptList [DecOpt.decOpt (τ = t) initSize]
          | .succ _ => some false),
        fun _ => none
      ]
    | .succ size' =>
      DecOpt.checkerBacktrack [
        (fun _ =>
          match Γ with
          | [] => some false
          | t :: _ => DecOpt.andOptList [DecOpt.decOpt (τ = t) initSize]),
        (fun _ =>
          match x with
          | .zero => some false
          | .succ x' =>
            match Γ with
            | [] => some false
            | τ' :: Γ' => DecOpt.andOptList [aux_arb initSize size' Γ' x' τ])
      ]
  fun size => aux_arb size size Γ x τ

/-- `lookup Γ x τ` is an instance of the `DecOpt` typeclass which describes
     partially decidable propositions -/
instance : DecOpt (lookup Γ x τ) where
  decOpt := checkLookup Γ x τ

-- Dummy `EnumSizedSuchThat` instance
-- TODO: implement metaprogramming infrastructure for deriving `EnumSizedSuchThat` instances
instance : EnumSizedSuchThat type (fun τ => typing Γ e τ) where
  enumSizedST := fun _ => OptionT.fail

/-- A handwritten checker which checks `typing Γ e τ`, ignoring the case for `App`
    (based on the auto-derived checker produced by QuickChick) -/
def checkTyping (Γ : List type) (e : term) (τ : type) : Nat → Option Bool :=
  let rec aux_arb (initSize : Nat) (size : Nat) (Γ : List type) (e : term) (τ : type) : Option Bool :=
    match size with
    | .zero =>
      DecOpt.checkerBacktrack [
        fun _ =>
          match e with
          | .Var x => DecOpt.andOptList [DecOpt.decOpt (lookup Γ x τ) initSize]
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
      DecOpt.checkerBacktrack [
        fun _ =>
          match e with
          | .Var x => DecOpt.andOptList [DecOpt.decOpt (lookup Γ x τ) initSize]
          | _ => some false,
        fun _ =>
          match τ with
          | .Nat =>
            match e with
            | .Add e1 e2 =>
              DecOpt.andOptList [
                aux_arb initSize size' Γ e1 .Nat,
                aux_arb initSize size' Γ e2 .Nat
              ]
            | _ => some false
          | _ => none,
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
              DecOpt.andOptList [
                  DecOpt.decOpt (τ1 = unkn_17_) initSize,
                  aux_arb initSize size' (τ1 :: Γ) e τ2
              ]
            | _ => none,
        fun _ =>
          match e with
          | .App (.Abs .Nat e1) e2 =>
            EnumeratorCombinators.enumeratingOpt
              (EnumSuchThat.enumST (fun t1 => typing Γ e2 t1))
              (fun t1 => aux_arb initSize size' Γ e1 (.Fun t1 τ))
              initSize
          | _ => some false
      ]
  fun size => aux_arb size size Γ e τ

/-- `typing Γ e τ` is an instance of the `DecOpt` typeclass which describes
     partially decidable propositions -/
instance : DecOpt (typing Γ e τ) where
  decOpt := checkTyping Γ e τ

-------------------------------------------------------------------------
-- Unconstrained generators
--------------------------------------------------------------------------

/-- A generator for STLC types, parameterized by its size argument -/
def genType : Nat → Gen type :=
  let rec arb_aux (size : Nat) : Gen type :=
    match size with
    | 0 => pure .Nat
    | .succ size' =>
        GeneratorCombinators.frequency (pure type.Nat)
          [(1, thunkGen $ fun _ => pure .Nat),
          (.succ size',
            thunkGen $ fun _ => do
              let p0 ← arb_aux size'
              let p1 ← arb_aux size'
              pure (.Fun p0 p1))]
  fun n => arb_aux n

/-- An enumerator for STLC types, parameterized by its size argument -/
def enumType : Nat → Enumerator type :=
  let rec enum_aux (size : Nat) : Enumerator type :=
    match size with
    | .zero => pure .Nat
    | .succ size' =>
      EnumeratorCombinators.oneOfWithDefault (pure .Nat)
        [
          pure .Nat,
          do
            let p0 ← enum_aux size'
            let p1 ← enum_aux size'
            pure (.Fun p0 p1)
        ]
  fun n => enum_aux n

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
                | _ :: Γ => do
                  let x ← aux_arb initSize size' Γ τ_0
                  return Nat.succ x))]
  fun size => aux_arb size size Γ τ

/-- `lookup Γ x τ` is an instance of the `ArbitrarySizedSuchThat` typeclass,
    which describes generators for values that satisfy a proposition -/
instance : ArbitrarySizedSuchThat Nat (fun x => lookup Γ x τ) where
  arbitrarySizedST := gen_lookup Γ τ

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
                let x ← ArbitrarySuchThat.arbitraryST (fun x => lookup G_0 x t_0)
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
                let x ← ArbitrarySuchThat.arbitraryST (fun x => lookup G_0 x t_0)
                return term.Var x)),
          (Nat.succ size',
            OptionTGen.thunkGen
              (fun _ => do
                let t1 ← SampleableExt.interpSample type
                let e2 ← aux_arb initSize size' G_0 t1
                let e1 ← aux_arb initSize size' G_0 (type.Fun t1 t_0)
                return term.App (.Abs .Nat e1) e2))]
  fun size => aux_arb size size G_ t_

/- `typing Γ e τ` is an instance of the `ArbitrarySizedSuchThat` typeclass,
    which describes generators for values that satisfy a proposition -/
-- instance : ArbitrarySizedSuchThat term (fun e => typing Γ e τ) where
--   arbitrarySizedST := gen_typing Γ τ
