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
