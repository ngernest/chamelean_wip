import Plausible.IR.Examples

----------------------------------------------------------------------------------
-- The `DecOpt` typeclass (adapted from QuickChick)
----------------------------------------------------------------------------------

/-- The `DecOpt` class encodes partial decidability:
     - It takes a `nat` argument as fuel
     - It returns `none`, if it can't decide.
     - It returns `some true/some false` if it can.
     - These are supposed to be monotonic, in the
       sense that if they ever return `some b` for
       some fuel, they will also do so for higher
       fuel values.

-/
class DecOpt (P : Prop) where
  decOpt : Nat → Option Bool

/-- All `Prop`s that have a `Decidable` instance (this includes `DecidableEq`)
    can be automatically given a `DecOpt` instance -/
instance [Decidable P] : DecOpt P where
  decOpt := fun _ =>
    if decide P then
      some true
    else
      some false


----------------------------------------------------------------------------------
-- Combinators for checkers (adapted from QuickChick sourcecode)
-- https://github.com/QuickChick/QuickChick/blob/master/src/Decidability.v
----------------------------------------------------------------------------------

/-- `checkerBacktrack` takes a list of checker handlers and returns:
    - `some true` if *any* handler does so
    - `some false` if *all* handlers do so
    - `none` otherwise -/
def checkerBacktrack (checkers : List (Unit → Option Bool)) : Option Bool :=
  let rec aux (l : List (Unit → Option Bool)) (b : Bool) : Option Bool :=
    match l with
    | c :: cs =>
      match c () with
      | some true => some true
      | some false => aux cs b
      | none => aux cs true
    | [] => if b then none else some false
  aux checkers false

--------------------------------------------------------------------------
-- Some example `DecOpt` instances
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

instance : DecOpt (typing Γ e τ) where
  decOpt := checkTyping Γ e τ
