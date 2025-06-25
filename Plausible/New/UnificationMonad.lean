
import Std
import Lean
import Plausible.New.Idents

open Lean Idents


abbrev Unknown := String
deriving instance Repr, BEq, Ord for Unknown

/-- *Ranges* represent sets of potential values (see section 4.2) -/
inductive Range
  | Undef (ty : String)
  | Fixed
  | Unknown (u : Unknown)
  | Ctr (ctor : String) (rs : List Range)
  deriving Repr, Inhabited

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

/-- Under the hood, this means `Unify α := UnifyState → Option (α × UnifyState)` -/
abbrev Unify (α : Type) := StateT UnifyState Option α

/-- `update u r` sets the range of the unknown `u` to be `r` -/
def update (u : Unknown) (r : Range) : Unify Unit :=
  fun s =>
    let k := s.constraints
    .some ((), { s with constraints := k.insert u r })

/-- Registers a new equality check between unknowns `u1` and `u2` -/
def equality (u1 : Unknown) (u2 : Unknown) : Unify Unit :=
  fun s =>
    let eqs := s.equalities
    .some ((), { s with equalities := eqs.merge {(u1, u2)} })

/-- Adds a new pattern match -/
def pattern (u : Unknown) (p : Pattern) : Unify Unit :=
  fun s =>
    let ps := s.patterns
    .some ((), { s with patterns := (u, p) :: ps})

/-- Returns a fresh unknown -/
def fresh_unknown (unknowns : Std.TreeSet Unknown) : Unknown :=
  let existingNames := Name.mkStr1 <$> unknowns.toArray
  toString $ genFreshName existingNames (Name.mkStr1 "unknown")

/-- Generaets and returns a new unknown -/
def fresh : Unify Unknown :=
  fun s =>
    let us := s.unknowns
    let u := fresh_unknown us
    .some (u, { s with unknowns := us.merge {u} })


----------------------------------
-- Unification algorithm (fig. 3)
mutual
  /-- Unifies two ranges -/
  partial def unify : Range → Range → Unify Unit
    | .Unknown u1, .Unknown u2 =>
      if u1 == u2 then
        return ()
      else do
        let k ← UnifyState.constraints <$> get
        let r1 := k.get! u1
        let r2 := k.get! u2
        unifyR (u1, r1) (u2, r2)
    | c1@(.Ctr _ _), c2@(.Ctr _ _) =>
      unifyC c1 c2
    | .Unknown u1, c2@(.Ctr _ _) => do
      let k ← UnifyState.constraints <$> get
      let r1 := k.get! u1
      unifyRC (u1, r1) c2
    | c1@(.Ctr _ _), .Unknown u2 => do
      let k ← UnifyState.constraints <$> get
      let r2 := k.get! u2
      unifyRC (u2, r2) c1
    | _, _ => failure

  /-- Unifies two `(Unknown, Range)` pairs -/
  partial def unifyR : Unknown × Range → Unknown × Range → Unify Unit
    | (u1, .Undef _), (u2, r2) => update u1 r2
    | (u1, r1), (u2, .Undef _) => update u2 r1
    | (u1, u1'@(.Unknown _)), (u2, r2) => unify u1' r2
    | (u1, r1), (u2, u2') => unify r1 u2'

  /-- Unifies two `Range`s that are both constructors -/
  partial def unifyC (r1 : Range) (r2 : Range) : Unify Unit :=
    match r1, r2 with
    | .Ctr c1 rs1, .Ctr c2 rs2 => sorry
    | _, _ => sorry

  /-- Unifies an `(Unknown, Range)` pair with a `Range -/
  partial def unifyRC (p1 : Unknown × Range) (r2 : Range) : Unify Unit :=
    let (u1, r1) := p1
    match r1, r2 with
    | _, .Ctr c2 rs2 => sorry
    | _, _ => sorry

end
