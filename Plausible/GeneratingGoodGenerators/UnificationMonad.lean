
import Std
import Lean
import Lean.Exception
import Plausible.New.Idents

open Lean Idents


--------------------------------------------------------------------------------
-- Adapted from "Generating Good Generators for Inductive Relations", POPL '18
--------------------------------------------------------------------------------

/-- An `Unknown` is just a Lean `Name` -/
abbrev Unknown := Name
deriving instance Repr, BEq for Unknown

/- Ord instance for `Name` (needed in order to use `HashMap`s with `Name`s as the key) -/
-- instance : Ord Name where
--   compare name1 name2 := compare name1.getString! name2.getString!

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

/-- A `ConstraintMap` maps `Unknown`s to `Range`s -/
abbrev ConstraintMap := Std.HashMap Unknown Range

/-- `UnifyState` stores the current state of the unification algorithm -/
structure UnifyState where
  /-- `constraints` maps unknowns to ranges -/
  constraints : ConstraintMap

  /-- `equalities` keeps track of equalities between unknowns
      that need to be checked -/
  equalities : Std.HashSet (Unknown × Unknown)

  /-- `patterns` contains a list of necessary pattern matches that
      need to be performed -/
  patterns : List (Unknown × Pattern)

  /-- A set of all existing unknowns -/
  unknowns : Std.HashSet Unknown

  deriving Repr

---------------------------------------------------------------
-- Unification monad (fig. 2 in Generating Good Generators)
---------------------------------------------------------------

/-- Under the hood, this means `UnifyM α := UnifyState → Option (α × UnifyState)` -/
abbrev UnifyM (α : Type) := StateT UnifyState Option α

namespace UnifyM

  /-- `update u r` sets the range of the unknown `u` to be `r` -/
  def update (u : Unknown) (r : Range) : UnifyM Unit :=
    modify $ fun s =>
      let k := s.constraints
      { s with constraints := k.insert u r }

  /-- More efficient: get constraints without separate `get` call -/
  def withConstraints {α : Type} (f : ConstraintMap → UnifyM α) : UnifyM α := do
    let state ← get
    f state.constraints

  /-- Directly applies a function `f` to the `constraint` map in the state  -/
  def modifyConstraints (f : ConstraintMap → ConstraintMap) : UnifyM Unit :=
    modify $ fun s => { s with constraints := f s.constraints }

   /-- Batches multiple constraint updates together for performance  -/
  def updateMany (updates : List (Unknown × Range)) : UnifyM Unit :=
    modifyConstraints $ fun constraints =>
      updates.foldl (fun acc (u, r) => acc.insert u r) constraints

  /-- Registers a new equality check between unknowns `u1` and `u2` -/
  def registerEquality (u1 : Unknown) (u2 : Unknown) : UnifyM Unit :=
    modify $ fun s =>
      let eqs := s.equalities
      { s with equalities := eqs.union {(u1, u2)} }

  /-- Adds a new pattern match -/
  def addPattern (u : Unknown) (p : Pattern) : UnifyM Unit :=
    modify $ fun s =>
      let ps := s.patterns
      { s with patterns := (u, p) :: ps }

  /-- Returns a fresh unknown -/
  def freshUnknown (unknowns : Std.HashSet Unknown) : Unknown :=
    let existingNames := unknowns.toArray
    genFreshName existingNames (Name.mkStr1 "unknown")

  /-- Generates and registers a new unknown in the `UnifyState` -/
  def registerFreshUnknown : UnifyM Unknown :=
    modifyGet $ fun s =>
      let us := s.unknowns
      let u := freshUnknown us
      (u, { s with unknowns := us.union {u} })

end UnifyM

------------------------------------------------------------------
-- Unification algorithm (fig. 3 of Generating Good Generators)
------------------------------------------------------------------

mutual
  /-- Top-level unification function which unifies the ranges mapped to by two unknowns -/
  partial def unify : Range → Range → UnifyM Unit
    | .Unknown u1, .Unknown u2 =>
      if u1 == u2 then
        return ()
      else UnifyM.withConstraints $ fun k => do
        let r1 := k.get! u1
        let r2 := k.get! u2
        unifyR (u1, r1) (u2, r2)
    | c1@(.Ctr _ _), c2@(.Ctr _ _) =>
      unifyC c1 c2
    | .Unknown u1, c2@(.Ctr _ _) =>
      UnifyM.withConstraints $ fun k => do
        let r1 := k.get! u1
        unifyRC (u1, r1) c2
    | c1@(.Ctr _ _), .Unknown u2 =>
      UnifyM.withConstraints $ fun k => do
        let r2 := k.get! u2
        unifyRC (u2, r2) c1
    | _, _ => panic! "reached catch-all case in unify"

  /-- Takes two `(Unknown, Range)` pairs & unifies them based on their `Range`s -/
  partial def unifyR : Unknown × Range → Unknown × Range → UnifyM Unit
    -- If the range of an unknown (e.g. `u1`) is undefined,
    -- we update `u1` to point to the range of `u2`
    | (u1, .Undef _), (_, r2) => UnifyM.update u1 r2
    | (_, r1), (u2, .Undef _) => UnifyM.update u2 r1
    | (_, u1'@(.Unknown _)), (_, r2) => unify u1' r2
    | (_, r1), (_, u2'@(.Unknown _)) => unify r1 u2'
    | (_, c1@(.Ctr _ _)), (_, c2@(.Ctr _ _)) => unifyC c1 c2
    | (u1, .Fixed), (u2, .Fixed) => do
      -- Assert that whatever the values of `u1` and `u2` are, they are equal
      -- Record this equality check using `equality`, then update `u1`'s range to the other
      UnifyM.registerEquality u1 u2
      UnifyM.update u1 .Fixed
    | (u1, .Fixed), (_, c2@(.Ctr _ _)) => handleMatch u1 c2
    | (_, c1@(.Ctr _ _)), (u2, .Fixed) => handleMatch u2 c1

  /-- Unifies two `Range`s that are both constructors -/
  partial def unifyC (r1 : Range) (r2 : Range) : UnifyM Unit :=
    match r1, r2 with
    | .Ctr c1 rs1, .Ctr c2 rs2 =>
      -- Recursively unify each of the constructor arguments
      -- Invariant: all ranges that appear as constructor args contain only constructors & unknowns
      if c1 == c2 && rs1.length == rs2.length then
        for (r1, r2) in (List.zip rs1 rs2) do
          unify r1 r2
      else
        failure
    | _, _ => panic! "Case not handled in unifyC"

  /-- Unifies an `(Unknown, Range)` pair with a `Range` -/
  partial def unifyRC : Unknown × Range → Range → UnifyM Unit
    | (u1, .Undef _), c2@(.Ctr _ _) => UnifyM.update u1 c2
    | (_, .Unknown u'), c2@(.Ctr _ _) =>
      UnifyM.withConstraints $ fun k => do
        let r := k.get! u'
        unifyRC (u', r) c2
    | (u, .Fixed), c2@(.Ctr _ _) => handleMatch u c2
    | (_, c1@(.Ctr _ _)), c2@(.Ctr _ _) => unifyC c1 c2
    | _, _ => panic! "reached catch-all case in unifyRC"

  /-- Corresponds to `match` in the pseudocode
     (we call this `handleMatch` since `match` is a reserved keyword in Lean) -/
  partial def handleMatch : Unknown → Range → UnifyM Unit
    | u, .Ctr c rs => do
      let p ← rs.mapM matchAux
      UnifyM.addPattern u (Pattern.Constructor c p)
    | _, _ => panic! "reached catch-all case in handleMatch"

  /-- `matchAux` traverses a `Range` and converts it into a
      pattern which can be used in a `match` expression -/
  partial def matchAux : Range → UnifyM Pattern
    | .Ctr c rs => do
      -- Recursively handle ranges
      let ps ← rs.mapM matchAux
      return (.Constructor c ps)
    | .Unknown u => UnifyM.withConstraints $ fun k => do
      let r := k.get! u
      match r with
      | .Undef _ => do
        -- Unknown becomes a pattern variable (bound by the pattern match)
        -- (i.e. the unknown serves as an input at runtime)
        -- We update `u`'s range to be `fixed`
        -- (since we're extracting information out of the scrutinee)
        UnifyM.update u .Fixed
        return (.Unknown u)
      | .Fixed => do
        -- Handles non-linear patterns:
        -- produce a fresh unknown `u'`, use `u'` as the pattern variable
        -- & enforce an equality check between `u` and `u'`
        let u' ← UnifyM.registerFreshUnknown
        UnifyM.registerEquality u' u
        UnifyM.update u' r
        return (.Unknown u')
      | u'@(.Unknown _) => matchAux u'
      | .Ctr c rs => do
        let ps ← rs.mapM matchAux
        return (.Constructor c ps)
    | _ => panic! "reached catch-all case in matchAux"

end

-------------
-- Tests
-------------

/-- Initial (empty) unification state  -/
def initUnifyState : UnifyState :=
  { constraints := ∅,
    equalities := ∅,
    patterns := [],
    unknowns := ∅ }

/-- Runs a `UnifyM unit` action using the empty `UnifyState`,
    returning the resultant `UnifyState` in an `Option`  -/
def runUnify (action : UnifyM Unit) : Option UnifyState :=
  Prod.snd <$> StateT.run action initUnifyState


/-- Test the nonempty trees example from Section 3 -/
def testNonemptyTrees : IO Unit := do
  -- Simulate: nonempty (Node x l r)
  -- This should unify successfully and bind unknowns

  let testUnify : UnifyM Unit := do
    -- Create unknowns for x, l, r, and the tree t
    let x ← UnifyM.registerFreshUnknown  -- will be "unknown0"
    let l ← UnifyM.registerFreshUnknown  -- will be "unknown1"
    let r ← UnifyM.registerFreshUnknown  -- will be "unknown2"
    let t ← UnifyM.registerFreshUnknown  -- will be "unknown3"

    -- Set up: t should be undefined (we want to generate it)
    -- Set up: x, l, r should be undefined (arbitrary values)
    UnifyM.updateMany [
      (t, .Undef "Tree"),
      (x, .Undef "Nat"),
      (l, .Undef "Tree"),
      (r, .Undef "Tree")
    ]

    -- Unify: t ~ Node x l r (from constructor conclusion)
    let nodePattern := Range.Ctr "Node" [.Unknown x, .Unknown l, .Unknown r]
    unify (.Unknown t) nodePattern

  match runUnify testUnify with
  | some finalState =>
    IO.println s!"✓ Nonempty trees test passed"
    IO.println s!"  Final constraints: {repr finalState.constraints.toList}"
    -- Should show t bound to Node unknown0 unknown1 unknown2
  | none =>
    IO.println "✗ Nonempty trees test failed"

/-- Test complete trees example: complete n t -/
def testCompleteTrees : IO Unit := do
  -- Simulate: complete in1 t where in1 is input, t is output

  let testUnify : UnifyM Unit := do
    let in1 ← UnifyM.registerFreshUnknown  -- input parameter
    let t ← UnifyM.registerFreshUnknown    -- output to generate
    let n ← UnifyM.registerFreshUnknown    -- universally quantified variable
    let l ← UnifyM.registerFreshUnknown    -- left subtree
    let r ← UnifyM.registerFreshUnknown    -- right subtree

    -- Set up modes: in1 is fixed input, t should be generated
    UnifyM.updateMany [
      (in1, .Fixed),
      (t, (.Undef "Tree")),
      (n, (.Undef "nat")),
      (l, (.Undef "Tree")),
      (r, (.Undef "Tree"))
    ]

    -- Unify constructor conclusion: complete (S n) (Node x l r) ~ complete in1 t
    let sn := Range.Ctr "S" [.Unknown n]
    let nodePattern := Range.Ctr "Node" [.Unknown $ Name.mkStr1 "x", .Unknown l, .Unknown r]

    -- This should create pattern match on in1
    unify (.Unknown in1) sn
    unify (.Unknown t) nodePattern

  match runUnify testUnify with
  | some finalState =>
    IO.println s!"✓ Complete trees test passed"
    IO.println s!"  Patterns generated: {repr finalState.patterns}"
    -- Should show pattern match on in1 against S n
  | none =>
    IO.println "✗ Complete trees test failed"


/-- Test binary search trees with bounds -/
def testBinarySearchTrees : IO Unit := do
  -- Simulate: bst lo hi (Node x l r) where lo, hi are inputs

  let testUnify : UnifyM Unit := do
    let lo ← UnifyM.registerFreshUnknown   -- lower bound (input)
    let hi ← UnifyM.registerFreshUnknown   -- upper bound (input)
    let t ← UnifyM.registerFreshUnknown    -- tree to generate
    let x ← UnifyM.registerFreshUnknown    -- node value
    let l ← UnifyM.registerFreshUnknown    -- left subtree
    let r ← UnifyM.registerFreshUnknown    -- right subtree

    -- Set up: lo, hi are fixed inputs
    UnifyM.updateMany [
      (lo, .Fixed),
      (hi, .Fixed),
      (t, (.Undef "Tree")),
      (x, (.Undef "nat")),
      (l, (.Undef "Tree")),
      (r, (.Undef "Tree"))
    ]

    -- Unify constructor conclusion: bst lo hi (Node x l r) ~ bst lo hi t
    let nodePattern := Range.Ctr "Node" [.Unknown x, .Unknown l, .Unknown r]
    unify (.Unknown t) nodePattern

    -- Simulate processing premises: lo < x, x < hi, bst lo x l, bst x hi r
    -- These would create additional constraints in a full implementation

  match runUnify testUnify with
  | some finalState =>
    IO.println s!"✓ BST test passed"
    IO.println s!"  Tree structure unified: {repr finalState.constraints}"
  | none =>
    IO.println "✗ BST test failed"


/-- Test non-linear patterns (same variable appears multiple times) -/
def testNonLinearPatterns : IO Unit := do
  -- Simulate: typing Γ (Abs t1 e) (Arr t1 t2)
  -- Note: t1 appears twice (non-linear)

  let testUnify : UnifyM Unit := do
    let gamma ← UnifyM.registerFreshUnknown  -- unknown_0
    let term ← UnifyM.registerFreshUnknown   -- unknown_1
    let typ ← UnifyM.registerFreshUnknown    -- unknown_2
    let t1 ← UnifyM.registerFreshUnknown     -- appears in both Abs and Arr
    let t2 ← UnifyM.registerFreshUnknown
    let e ← UnifyM.registerFreshUnknown

    -- Set up: gamma, term, typ are inputs
    UnifyM.updateMany [
      (gamma, .Fixed),
      (term, .Fixed),
      (typ, .Fixed),
      (t1, (.Undef "type")),
      (t2, (.Undef "type")),
      (e, (.Undef "term"))
    ]

    -- Create patterns with t1 appearing twice
    let absPattern := Range.Ctr "Abs" [.Unknown t1, .Unknown e]
    let arrPattern := Range.Ctr "Arr" [.Unknown t1, .Unknown t2]

    -- This should trigger pattern matching on term and typ
    unify (.Unknown term) absPattern
    unify (.Unknown typ) arrPattern

    -- The non-linearity of t1 should create equality constraints (unknown_3, unknown_6)

  match runUnify testUnify with
  | some finalState =>
    IO.println s!"✓ Non-linear patterns test passed"
    IO.println s!"  Patterns: {repr finalState.patterns}"
    IO.println s!"  Equalities: {repr finalState.equalities.toList}"
    -- Should show pattern matches and equality constraints for t1
  | none =>
    IO.println "✗ Non-linear patterns test failed"

/-- Test function calls in constructor conclusions -/
def testFunctionCalls : IO Unit := do
  -- Simulate: square_of n (n * n) -> square_of n m
  -- where (n * n) needs to be converted to fresh variable with equality

  let testUnify : UnifyM Unit := do
    let n ← UnifyM.registerFreshUnknown
    let m ← UnifyM.registerFreshUnknown
    let in1 ← UnifyM.registerFreshUnknown  -- first argument (input)
    let in2 ← UnifyM.registerFreshUnknown  -- second argument (input)

    -- Set up: inputs are fixed, n, m need to be determined
    UnifyM.updateMany [
      (in1, .Fixed),
      (in2, .Fixed),
      (n, .Undef "nat"),
      (m, .Undef "nat")
    ]

    -- Unify: `square_of n (n * n) ~ square_of in1 in2`
    -- This should unify `n` with `in1`
    unify (.Unknown n) (.Unknown in1)

    -- The `(n * n)` part would normally create a fresh variable and equality
    -- For testing, we'll simulate this by creating an equality constraint
    let product ← UnifyM.registerFreshUnknown
    UnifyM.update product (.Undef "nat")
    UnifyM.registerEquality product in2  -- product should equal in2

    -- Simulate the equality: product = n * n (would be handled by preprocessing)

  match runUnify testUnify with
  | some finalState =>
    IO.println s!"✓ Function calls test passed"
    IO.println s!"  Equalities created: {repr finalState.equalities.toList}"
  | none =>
    IO.println "✗ Function calls test failed"


/-- Run all test cases -/
def runAllTests : IO Unit := do
  IO.println "=== Testing Unification Monad ==="
  IO.println ""

  testNonemptyTrees
  IO.println ""

  testCompleteTrees
  IO.println ""

  testBinarySearchTrees
  IO.println ""

  testNonLinearPatterns
  IO.println ""

  testFunctionCalls
  IO.println ""

  IO.println "=== All tests completed ==="

-- #eval runAllTests
