
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



----------------------------------
-- Unification algorithm (fig. 3)
mutual
  def unify (u1 : Unknown) (u2 : Unknown) : Unify Unit :=
    sorry

  def unifyR (p1 : Unknown × Range) (p2 : Unknown × Range) : Unify Unit :=
    let (u1, r) := p1
    let (u2, r) := p2
    sorry

  def unifyC (r1 : Range) (r2 : Range) : Unify Unit :=
    match r1, r2 with
    | .Ctr c1 rs1, .Ctr c2 rs2 => sorry
    | _, _ => sorry

  def unifyRC (p1 : Unknown × Range) (r2 : Range) : Unify Unit :=
    let (u1, r1) := p1
    match r1, r2 with
    | _, .Ctr c2 rs2 => sorry
    | _, _ => sorry

end
