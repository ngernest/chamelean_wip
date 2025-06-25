
import Std

abbrev Unknown := String
deriving instance Repr, BEq, Ord for Unknown

/-- *Ranges* represent sets of potential values (see section 4.2) -/
inductive Range
  | Undef (ty : Type)
  | Fixed
  | Unknown (u : Unknown)
  | Ctr (ctor : String) (rs : List Range)
  deriving Repr

inductive Pattern
  | Unknown : String -> Pattern
  | Constructor : String -> List Pattern -> Pattern
  deriving Repr

structure UnifyState where
  constraints : Std.TreeMap Unknown Range (cmp := compare)
  equalities : Std.TreeSet (Unknown × Unknown) (cmp := compare)
  patterns : List (Unknown × Pattern)
  unknowns : Std.TreeSet Unknown (cmp := compare)
  deriving Repr

-- Unification monad (fig. 2)

abbrev Unify (α : Type) := UnifyState → Option (α × UnifyState)

def update (u : Unknown) (r : Range) : Unify Unit :=
  fun s =>
    let k := s.constraints
    .some ((), { s with constraints := k.insert u r })

def equality (u1 : Unknown) (u2 : Unknown) : Unify Unit :=
  fun s =>
    let eqs := s.equalities
    .some ((), { s with equalities := eqs.merge {(u1, u2)} })

def pattern (u : Unknown) (p : Pattern) : Unify Unit :=
  fun s =>
    let ps := s.patterns
    .some ((), { s with patterns := (u, p) :: ps})

/-- Returns a fresh unknown -/
def fresh_unknown (us : Std.TreeSet Unknown) : Unknown := sorry

def fresh : Unify Unknown :=
  fun s =>
    let us := s.unknowns
    let u := fresh_unknown us
    .some (u, { s with unknowns := us.merge {u} })
