import Plausible.IR.Examples

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
-- Some example checkers
--------------------------------------------------------------------------

/-- A handwritten checker which checks `lookup Γ x τ`
  (modelled after the automatically derived checker produced by QuickChick). -/
def checkLookup (Γ : List type) (x : Nat) (τ : type) : Nat → Option Bool :=
  let rec aux_arb (size : Nat) (Γ : List type) (x : Nat) (τ : type) : Option Bool :=
    match size with
    | .zero =>
      checkerBacktrack [
        (fun _ =>
          match x with
          | .zero =>
            match Γ with
            | [] => some false
            | t :: _ =>
              if (τ = t) then some true else some false
          | .succ _ => some false),
        fun _ => none
      ]
    | .succ size' =>
      checkerBacktrack [
        (fun _ =>
          match Γ with
          | [] => some false
          | t :: _ =>
            match decide (τ = t) with
            | true => some true
            | false => some false),
        (fun _ =>
          match x with
          | .zero => some false
          | .succ x' =>
            match Γ with
            | [] => some false
            | _ :: Γ' =>
              match aux_arb size' Γ' x' τ with
              | some true => some true
              | some false => some false
              | none => none)
      ]
  fun size => aux_arb size Γ x τ


/-- A handwritten checker which checks `typing Γ e τ`, ignoring the case for `App`
    (based on the auto-derived checker produced by QuickChick) -/
def checkTyping (Γ : List type) (e : term) (τ : type) : Nat → Option Bool :=
  let rec aux_arb (init_size : Nat) (size : Nat) (Γ : List type) (e : term) (τ : type) : Option Bool :=
    match size with
    | .zero =>
      checkerBacktrack [
        fun _ =>
          match e with
          | .Var x => checkLookup Γ x τ init_size
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
          | .Var x => checkLookup Γ x τ init_size
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
              match decide (τ1 = unkn_17_) with
              | true => aux_arb init_size size' (τ1 :: Γ) e τ2
              | false => some false
            | _ => none,
        -- TODO: handle App case
      ]
  fun size => aux_arb size size Γ e τ
