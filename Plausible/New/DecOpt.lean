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
