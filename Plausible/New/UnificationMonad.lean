
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

/-- A `Pattern` is either an unknown or a fully-applied constructor -/
inductive Pattern
  | Unknown : Unknown -> Pattern
  | Constructor : String -> List Pattern -> Pattern
  deriving Repr, Inhabited

/-- A structure which stores the current state of the unification algorithm -/
structure UnifyState where
  /-- `constraints` maps unknowns to ranges -/
  constraints : Std.TreeMap Unknown Range (cmp := compare)

  /-- `equalities` keeps track of equalities between unknowns
      that need to be checked -/
  equalities : Std.TreeSet (Unknown × Unknown) (cmp := compare)

  /-- `patterns` contains a list of necessary pattern matches that
      need to be performed -/
  patterns : List (Unknown × Pattern)

  /-- A set of all existing unknowns -/
  unknowns : Std.TreeSet Unknown (cmp := compare)
  deriving Repr

-- Unification monad (fig. 2)

/-- Under the hood, this means `Unify α := UnifyState → Option (α × UnifyState)` -/
abbrev Unify (α : Type) := StateT UnifyState Option α

/-- `update u r` sets the range of the unknown `u` to be `r` -/
def update (u : Unknown) (r : Range) : Unify Unit :=
  modify $ fun s =>
    let k := s.constraints
    { s with constraints := k.insert u r }

/-- Registers a new equality check between unknowns `u1` and `u2` -/
def equality (u1 : Unknown) (u2 : Unknown) : Unify Unit :=
  modify $ fun s =>
    let eqs := s.equalities
    { s with equalities := eqs.merge {(u1, u2)} }

/-- Adds a new pattern match -/
def pattern (u : Unknown) (p : Pattern) : Unify Unit :=
  modify $ fun s =>
    let ps := s.patterns
    { s with patterns := (u, p) :: ps}

/-- Returns a fresh unknown -/
def fresh_unknown (unknowns : Std.TreeSet Unknown) : Unknown :=
  let existingNames := Name.mkStr1 <$> unknowns.toArray
  toString $ genFreshName existingNames (Name.mkStr1 "unknown")

/-- Generates and returns a new unknown -/
def fresh : Unify Unknown :=
  modifyGet $ fun s =>
    let us := s.unknowns
    let u := fresh_unknown us
    (u, { s with unknowns := us.merge {u} })

----------------------------------
-- Unification algorithm (fig. 3)
----------------------------------
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
    | _, _ => panic! "reached catch-all case in unify"

  /-- Unifies two `(Unknown, Range)` pairs -/
  partial def unifyR : Unknown × Range → Unknown × Range → Unify Unit
    | (u1, .Undef _), (_, r2) => update u1 r2
    | (_, r1), (u2, .Undef _) => update u2 r1
    | (_, u1'@(.Unknown _)), (_, r2) => unify u1' r2
    | (_, r1), (_, u2'@(.Unknown _)) => unify r1 u2'
    | (_, c1@(.Ctr _ _)), (_, c2@(.Ctr _ _)) => unifyC c1 c2
    | (u1, .Fixed), (u2, .Fixed) => do
      equality u1 u2
      update u1 .Fixed
    | (u1, .Fixed), (_, c2@(.Ctr _ _)) => handleMatch u1 c2
    | (_, c1@(.Ctr _ _)), (u2, .Fixed) => handleMatch u2 c1

  /-- Unifies two `Range`s that are both constructors -/
  partial def unifyC (r1 : Range) (r2 : Range) : Unify Unit :=
    match r1, r2 with
    | .Ctr c1 rs1, .Ctr c2 rs2 =>
      if c1 == c2 && rs1.length == rs2.length then
        for (r1, r2) in (List.zip rs1 rs2) do
          unify r1 r2
      else
        failure
    | _, _ => panic! "Case not handled in unifyC"

  /-- Unifies an `(Unknown, Range)` pair with a `Range -/
  partial def unifyRC : Unknown × Range → Range → Unify Unit
    | (u1, .Undef _), c2@(.Ctr _ _) => update u1 c2
    | (_, .Unknown u'), c2@(.Ctr _ _) => do
      let k ← UnifyState.constraints <$> get
      let r := k.get! u'
      unifyRC (u', r) c2
    | (u, .Fixed), c2@(.Ctr _ _) => handleMatch u c2
    | (_, c1@(.Ctr _ _)), c2@(.Ctr _ _) => unifyC c1 c2
    | _, _ => panic! "reached catch-all case in unifyRC"

  /-- Corresponds to `match` in the pseudocode
     (we call this `handleMatch` since `match` is a reserved keyword in Lean) -/
  partial def handleMatch : Unknown → Range → Unify Unit
    | u, .Ctr c rs => do
      let p ← rs.mapM matchAux
      pattern u (Pattern.Constructor c p)
    | _, _ => panic! "reached catch-all case in handleMatch"

  /-- `matchAux` traverses a `Range` and converts it into a
      pattern which can be used in a `match` expression -/
  partial def matchAux : Range → Unify Pattern
    | .Ctr c rs => do
      -- Recursively handle ranges
      let ps ← rs.mapM matchAux
      return (.Constructor c ps)
    | .Unknown u => do
      let k ← UnifyState.constraints <$> get
      let r := k.get! u
      match r with
      | .Undef _ => do
        -- Unknown becomes a pattern variable (bound by the pattern match)
        -- (i.e. the unknown serves as an input at runtime)
        update u .Fixed
        return (.Unknown u)
      | .Fixed => do
        -- Handles non-linear patterns
        let u' ← fresh
        equality u' u
        update u' r
        return (.Unknown u')
      | u'@(.Unknown _) => matchAux u'
      | .Ctr c rs => do
        let ps ← rs.mapM matchAux
        return (.Constructor c ps)
    | _ => panic! "reached catch-all case in matchAux"

end
