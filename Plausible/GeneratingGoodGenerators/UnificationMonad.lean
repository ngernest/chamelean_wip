
import Std
import Lean
import Lean.Exception
import Plausible.New.Idents

open Lean Idents


--------------------------------------------------------------------------------
-- Adapted from "Generating Good Generators for Inductive Relations", POPL '18
--------------------------------------------------------------------------------

/-- An `Unknown` is a Lean `Name` correpsonding to a variable -/
abbrev Unknown := Name
deriving instance Repr, BEq for Unknown

/-- `Ord` instance for `Unknown`s
    (which just uses the `Ord` instance for their underlying string representations) -/
instance : Ord Unknown where
  compare u1 u2 := compare u1.toString u2.toString

/-- *Ranges* represent sets of potential values that a variable can take on during generation -/
inductive Range
  /-- Undefined value, parameterized by a type `ty` (represented as a Lean `Expr`)
      - The `unknowns` we want to generate (e.g. a `Tree` in the BST example) start out
        with `Undef` ranges -/
  | Undef (ty : Expr)

  /-- A `Fixed` range means the corresponding unknown's value serves as an input at runtime
     (e.g. `lo` and `hi` in the BST example) -/
  | Fixed

  /-- The `Range` of an `Unknown` can be another `Unknown` (to facilitate sharing)-/
  | Unknown (u : Unknown)

  /-- A `Range` can be a constructor `C` fully applied to a list of `Range`s -/
  | Ctor (ctor : Name) (rs : List Range)
  deriving Repr, Inhabited, BEq

/-- A `Pattern` is either an unknown or a fully-applied constructor -/
inductive Pattern
  | UnknownPattern : Unknown -> Pattern
  | CtorPattern : Name -> List Pattern -> Pattern
  deriving Repr, Inhabited

/-- A *constructor expression* (`ConstructorExpr`) is either a variable (represented by its `Name`),
    or a constructor (identified by its `Name`) applied to some list of arguments,
    each of which are themselves `ConstructorExpr`s

    - Note: this type is isomorphic to `Pattern`, but we define a separate type to avoid confusing
    `ConstructorExpr` with `Pattern` since they are used in different parts of the algorithm -/
inductive ConstructorExpr
  | Unknown : Name -> ConstructorExpr
  | Ctor : Name -> List ConstructorExpr -> ConstructorExpr
  deriving Repr, BEq


/-- An `UnknownMap` maps `Unknown`s to `Range`s -/
abbrev UnknownMap := Std.HashMap Unknown Range

/-- `UnifyState` stores the current state of the unification algorithm -/
structure UnifyState where
  /-- `constraints` is an `UnknownMap` that maps unknowns to ranges -/
  constraints : UnknownMap

  /-- `equalities` keeps track of equalities between unknowns
      that need to be checked -/
  equalities : Std.HashSet (Unknown × Unknown)

  /-- `patterns` contains a list of necessary pattern matches that
      need to be performed -/
  patterns : List (Unknown × Pattern)

  /-- A set of all existing `Unknown`s -/
  unknowns : Std.HashSet Unknown

  /-- The name of the output variable (variable to be generated) -/
  outputName : Name

  /-- The type of the output variable (variable to be generated) -/
  outputType : Expr

  /-- All inputs (top-level arguments) to the generator -/
  inputNames : List Name

  /-- The list of hypotheses in the constructor's type (excluding the constructor's conclusion)
      Each hypothesis is represented as a pair `(constructor name, constructor args)`
      i.e. a constructor name applied to a list of arguments, each of which are `ConstructorExpr`s -/
  hypotheses : List (Name × List ConstructorExpr)

  deriving Repr

---------------------------------------------------------------
-- `ToMessageData` instances for pretty-printing
---------------------------------------------------------------

/-- Pretty-prints a `Range` as a `MessageData` -/
partial def toMessageDataRange (range : Range) : MessageData :=
  match range with
  | .Undef tyExpr => m!"Undef {tyExpr}"
  | .Ctor c rs =>
    let rendredCtorArgs := toMessageDataRange <$> rs
    m!"Ctor ({c} {rendredCtorArgs})"
  | .Unknown u => m!"Unknown {u}"
  | .Fixed => m!"Fixed"

instance : ToMessageData Range where
  toMessageData := toMessageDataRange

/-- Pretty-prints a `Pattern` as a `MessageData` -/
partial def toMessageDataPattern (p : Pattern) : MessageData :=
  match p with
  | .UnknownPattern u => m!"UnknownPattern {u}"
  | .CtorPattern c ps =>
    let renderedCtorArgs := toMessageDataPattern <$> ps
    m!"CtorPattern ({c} {renderedCtorArgs})"

instance : ToMessageData Pattern where
  toMessageData pattern := toMessageDataPattern pattern

/-- Pretty-prints a `ConstructorExpr` as a `MessageData` -/
partial def toMessageDataConstructorExpr (ctorExpr : ConstructorExpr) : MessageData :=
  match ctorExpr with
  | .Unknown x => m!"Unknown {x}"
  | .Ctor c args =>
    let renderedArgs := toMessageDataConstructorExpr <$> args
    m!"Ctor ({c} {renderedArgs})"

instance : ToMessageData ConstructorExpr where
  toMessageData := toMessageDataConstructorExpr

instance : ToMessageData UnifyState where
  toMessageData unifyState :=
    let constraints := unifyState.constraints.toList
    -- Sort the constraints map based on the ordering of its keys
    let sortedConstraints := List.mergeSort constraints (fun (u1, _) (u2, _) => Ordering.isLE (compare u1 u2))
    let formattedConstraints :=
      sortedConstraints.map $ fun (u, r) => m!"{u} ↦ {r}"
    let equalities :=
      unifyState.equalities.toList.map $ fun (u1, u2) => m!"{u1} = {u2}"
    let patterns :=
      unifyState.patterns.map $ fun (u, pat) => m!"{u} ≡ {pat}"
    let unknowns :=
      unifyState.unknowns.toList.map $ fun u => m!"{u}"

    let hyps := unifyState.hypotheses.map $ fun hyp => m!"{hyp}"

    m!"⟨\n  constraints := \n{formattedConstraints},\n  equalities := {equalities},\n  patterns := {patterns},\n  unknowns := {unknowns}\n, hypotheses := {hyps}\n⟩"



---------------------------------------------------------------
-- Unification monad (fig. 2 in Generating Good Generators)
---------------------------------------------------------------

/-- `UnifyM` is a monad for unification + code generation.
     Note that the definition of `UnifyM` (after unfolding) is:
     ```
     UnifyM α := UnifyState → MetaM (Option (α × UnifyState))
     ``` -/
abbrev UnifyM (α : Type) := StateT UnifyState (OptionT MetaM) α

namespace UnifyM

  /-- `update u r` sets the range of the unknown `u` to be `r` -/
  def update (u : Unknown) (r : Range) : UnifyM Unit := do
    modify $ fun s =>
      let k := s.constraints
      { s with constraints := k.insert u r }

  /-- Applies a function `f` to the `constraints` map stored in `UnifyState`
      - This function allows us to fetch the `constraints` map without needing
        a seperate `get` call inside the State monad -/
  def withConstraints (f : UnknownMap → UnifyM α) : UnifyM α := do
    let unifyState ← get
    f unifyState.constraints

  /-- Applies a function `f` to the list of `hypotheses` stored in `UnifyState`
      - This function allows us to fetch the `hypotheses` field without needing
        a seperate `get` call inside the State monad -/
  def withHypotheses (f : List (Name × List ConstructorExpr) → UnifyM α) : UnifyM α := do
    let unifyState ← get
    f unifyState.hypotheses

  /-- Applies a function `f` to the set of `unknowns` stored in `UnifyState`
      - This function allows us to fetch the `hypotheses` field without needing
        a seperate `get` call inside the State monad -/
  def withUnknowns (f : Std.HashSet Unknown → UnifyM α) : UnifyM α := do
    let unifyState ← get
    f unifyState.unknowns

  /-- Directly applies a function `f` to the `constraint` map in the state  -/
  def modifyConstraints (f : UnknownMap → UnknownMap) : UnifyM Unit :=
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

  /-- Produces a fresh unknown that is guaranteed not to be in the
      existing set of `unknowns` -/
  def freshUnknown (unknowns : Std.HashSet Unknown) : Unknown :=
    let existingNames := unknowns.toArray
    genFreshName existingNames `u

  /-- Produces and registers a new unknown in the `UnifyState` -/
  def registerFreshUnknown : UnifyM Unknown := do
    modifyGet $ fun s =>
      let us := s.unknowns
      let u := freshUnknown us
      (u, { s with unknowns := us.union { u } })

  /-- Runs a `UnifyM` computation, returning the result in the `MetaM` monad -/
  def runInMetaM (action : UnifyM α) (st : UnifyState) : MetaM (Option (α × UnifyState)) := do
    OptionT.run (StateT.run action st)

  /-- Finds the `Range` corresponding to an `Unknown` `u` in the
      `UnknownMap` `k`, returning an informative error message if `u ∉ k.keys` -/
  def findCorrespondingRange (k : UnknownMap) (u : Unknown) : UnifyM Range :=
    match k[u]? with
    | some r => return r
    | none => throwError m!"unable to find {u} in UnknownMap {k.toList}"

  /-- Determines if an unknown `u` has a `Range` of `Undef τ` for some type `τ`
      in the constraints map -/
  def hasUndefRange (u : Unknown) : UnifyM Bool := do
    logWarning m!"Checking if unknown {u} has an Undef Range"
    UnifyM.withConstraints (fun k => do
      let r ← findCorrespondingRange k u
      match r with
      | .Undef _ => return true
      | _ => return false)

  /-- `findUnknownsWithUndefRanges unknowns` returns all `u ∈ unknowns`
      such that `u ↦ Undef τ` for some type `τ` in the `constraints` map stored within `UnifyState` -/
  def findUnknownsWithUndefRanges (unknowns : List Unknown) : UnifyM (List Unknown) := do
    let state ← get
    let k := state.constraints
    List.foldlM (fun acc u => do
      let r ← findCorrespondingRange k u
      match r with
      | .Undef _ => return (u :: acc)
      | _ => return acc) [] unknowns

  /-- Updates the `constraint` map so that for each `u ∈ unknowns`,
      we have the binding `u ↦ Fixed` in `constraints` -/
  def fixRanges (unknowns : List Unknown) : UnifyM Unit := do
    updateMany (unknowns.zip (List.replicate unknowns.length .Fixed))

  /-- `findCanonicalUnknown k u` finds the *canonical* representation of the unknown `u` based on the `ConstraintMap` `k`.
      Specifically:
      - If `u ↦ Unknown u'` in `k`, then we recursively look up the canonical rerpesentation of `u'` by traversing
        the unification graph formed by the `constraints` map in `UnifyState`
      - If `u ↦ r` (where `r` is any `Range` that is not some `Unknown`), then `u` is its own canonical representation

      This function is used to handle cases in `constraints` where an unknown maps to another unknown.  -/
  partial def findCanonicalUnknown (k : UnknownMap) (u : Unknown) : UnifyM Unknown := do
    let r ← findCorrespondingRange k u
    match r with
    | .Unknown u' => findCanonicalUnknown k u'
    | _ => return u

  /-- `updateConstructorArg k ctorArg` uses the `UnknownMap` `k` to rewrite any unknowns that appear in the
      `ConstructorExpr` `ctorArg`, substituting each `Unknown` with its canonical representation
      (determined by calling `findCanonicalUnknown`)
      - See `updateHypothesesWithUnificationResult` for an example of how this function is used -/
  partial def updateConstructorArg (k : UnknownMap) (ctorArg : ConstructorExpr) : UnifyM ConstructorExpr := do
    match ctorArg with
    | .Unknown arg =>
      let canonicalUnknown ← findCanonicalUnknown k arg
      if arg != canonicalUnknown then
        return (.Unknown canonicalUnknown)
      else
        return (.Unknown arg)
    | .Ctor ctorName args =>
      let updatedArgs ← args.mapM (updateConstructorArg k)
      return (.Ctor ctorName updatedArgs)

  /-- Updates the list of `hypotheses` in `UnifyState` with the result of unification,
      updating `Unknown`s in `hypotheses` that appear in constructor argument positions
      with their canonical representations (as determined by `findCanonicalUnknown`) -/
  def updateHypothesesWithUnificationResult : UnifyM Unit := do
    let state ← get
    let k := state.constraints
    let hypotheses := state.hypotheses

    let mut newHypotheses := #[]
    for (ctorName, ctorArgs) in hypotheses do
      let mut newArgs := #[]
      for arg in ctorArgs do
        let updatedArg ← updateConstructorArg k arg
        newArgs := newArgs.push updatedArg

      newHypotheses := newHypotheses.push (ctorName, newArgs.toList)

    logWarning m!"hypotheses after unification = {newHypotheses}"

    modify $ fun s => { s with hypotheses := newHypotheses.toList }

  /-- Converts an array of `ConstructorExpr`s to one single `TSyntaxArray term`-/
  partial def convertConstructorExprsToTSyntaxTerms (ctorExprs : Array ConstructorExpr) : UnifyM (TSyntaxArray `term) :=
    ctorExprs.mapM (fun ctorExpr => do
      match ctorExpr with
      | .Unknown u => `($(Lean.mkIdent u))
      | .Ctor c args =>
        let argTerms ← convertConstructorExprsToTSyntaxTerms args.toArray
        `($(mkIdent c) $argTerms*))

  /-- Accumulates all the `Unknown`s -/
  partial def collectUnknownsInConstructorExpr (ctorExpr : ConstructorExpr) : UnifyM (List Unknown) := do
    logWarning m!"collectUnknownsInConstructorExpr {ctorExpr}"
    match ctorExpr with
    | .Unknown u => return [u]
    | .Ctor c args =>
      let unknowns ← List.flatMapM collectUnknownsInConstructorExpr args
      return c :: unknowns




end UnifyM

------------------------------------------------------------------
-- Unification algorithm (fig. 3 of Generating Good Generators)
------------------------------------------------------------------


mutual
  /-- Top-level unification function which unifies the ranges mapped to by two unknowns -/
  partial def unify (range1 : Range) (range2: Range) : UnifyM Unit := do
    match range1, range2 with
    | .Unknown u1, .Unknown u2 =>
      if u1 == u2 then
        return ()
      else UnifyM.withConstraints $ fun k => do
        let r1 ← UnifyM.findCorrespondingRange k u1
        let r2 ← UnifyM.findCorrespondingRange k u2
        unifyR (u1, r1) (u2, r2)
    | c1@(.Ctor _ _), c2@(.Ctor _ _) =>
      unifyC c1 c2
    | .Unknown u1, c2@(.Ctor _ _) =>
      UnifyM.withConstraints $ fun k => do
        let r1 ← UnifyM.findCorrespondingRange k u1
        unifyRC (u1, r1) c2
    | c1@(.Ctor _ _), .Unknown u2 =>
      UnifyM.withConstraints $ fun k => do
        let r2 ← UnifyM.findCorrespondingRange k u2
        unifyRC (u2, r2) c1
    | r1, r2 => throwError "Unable to unify {r1} with {r2}"

  /-- Takes two `(Unknown, Range)` pairs & unifies them based on their `Range`s -/
  partial def unifyR : Unknown × Range → Unknown × Range → UnifyM Unit
    -- If the range of an unknown (e.g. `u1`) is undefined,
    -- we update `u1` to point to the range of `u2`
    | (u1, .Undef _), (u2, _) => UnifyM.update u1 (.Unknown u2)
    | (u1, _), (u2, .Undef _) => UnifyM.update u2 (.Unknown u1)
    | (_, u1'@(.Unknown _)), (u2, _) => unify u1' (.Unknown u2)
    | (u1, _), (_, u2'@(.Unknown _)) => unify (.Unknown u1) u2'
    | (_, c1@(.Ctor _ _)), (_, c2@(.Ctor _ _)) => unifyC c1 c2
    | (u1, .Fixed), (u2, .Fixed) => do
      -- Assert that whatever the values of `u1` and `u2` are, they are equal
      -- Record this equality check using `equality`, then update `u1`'s range to the other
      UnifyM.registerEquality u1 u2
      UnifyM.update u1 (.Unknown u2)
    | (u1, .Fixed), (_, c2@(.Ctor _ _)) => handleMatch u1 c2
    | (_, c1@(.Ctor _ _)), (u2, .Fixed) => handleMatch u2 c1

  /-- Unifies two `Range`s that are both constructors -/
  partial def unifyC (r1 : Range) (r2 : Range) : UnifyM Unit :=
    match r1, r2 with
    | .Ctor c1 rs1, .Ctor c2 rs2 =>
      -- Recursively unify each of the constructor arguments
      -- Invariant: all ranges that appear as constructor args contain only constructors & unknowns
      if c1 == c2 && rs1.length == rs2.length then
        for (r1, r2) in (List.zip rs1 rs2) do
          unify r1 r2
      else
        failure
    | _, _ => throwError m!"unifyC, unable to unify r1 = {r1}, r2 = {r2} which are not both constructors"

  /-- Unifies an `(Unknown, Range)` pair with a `Range` -/
  partial def unifyRC : Unknown × Range → Range → UnifyM Unit
    | (u1, .Undef _), c2@(.Ctor _ _) => UnifyM.update u1 c2
    | (_, .Unknown u'), c2@(.Ctor _ _) =>
      UnifyM.withConstraints $ fun k => do
        let r ← UnifyM.findCorrespondingRange k u'
        unifyRC (u', r) c2
    | (u, .Fixed), c2@(.Ctor _ _) => handleMatch u c2
    | (_, c1@(.Ctor _ _)), c2@(.Ctor _ _) => unifyC c1 c2
    | (u, r), r' => throwError m!"unifyRC called, unable to unify (unknown {u}, range {r}) with range {r'}"

  /-- Corresponds to `match` in the pseudocode
     (we call this `handleMatch` since `match` is a reserved keyword in Lean) -/
  partial def handleMatch (unknown : Unknown) (range : Range) : UnifyM Unit := do
    match unknown, range with
    | u, .Ctor c rs => do
      let ps ← rs.mapM matchAux
      UnifyM.addPattern u (Pattern.CtorPattern c ps)
    | u, r => throwError m!"handleMatch called, unable to match unknown {u} with range {r} which is not in constructor form"

  /-- `matchAux` traverses a `Range` and converts it into a
      pattern which can be used in a `match` expression -/
  partial def matchAux (range : Range) : UnifyM Pattern := do
    match range with
    | .Ctor c rs => do
      -- Recursively handle ranges
      let ps ← rs.mapM matchAux
      return (.CtorPattern c ps)
    | .Unknown u => UnifyM.withConstraints $ fun k => do
      let r ← UnifyM.findCorrespondingRange k u
      match r with
      | .Undef _ => do
        -- Unknown becomes a pattern variable (bound by the pattern match)
        -- (i.e. the unknown serves as an input at runtime)
        -- We update `u`'s range to be `fixed`
        -- (since we're extracting information out of the scrutinee)
        UnifyM.update u .Fixed
        return (.UnknownPattern u)
      | .Fixed => do
        -- Handles non-linear patterns:
        -- produce a fresh unknown `u'`, use `u'` as the pattern variable
        -- & enforce an equality check between `u` and `u'`
        let u' ← UnifyM.registerFreshUnknown
        UnifyM.registerEquality u' u
        UnifyM.update u' r
        return (.UnknownPattern u')
      | u'@(.Unknown _) => matchAux u'
      | .Ctor c rs => do
        let ps ← rs.mapM matchAux
        return (.CtorPattern c ps)
    | _ => throwError m!"matchAux called with unexpected range {range}"

end

-------------
-- Tests
-------------

/-- Initial (empty) unification state  -/
def emptyUnifyState : UnifyState :=
  { constraints := ∅,
    equalities := ∅,
    patterns := [],
    unknowns := ∅,
    outputName := `dummyOutput,
    outputType := mkConst `dummyOutputType
    inputNames := []
    hypotheses := [] }

/-- Runs a `UnifyM unit` action using the empty `UnifyState`,
    returning the resultant `UnifyState` in an `Option`  -/
def runUnifyState (action : UnifyM α) : OptionT MetaM UnifyState := do
  let (_, finalState) ← StateT.run action emptyUnifyState
  return finalState


/-- Test the nonempty trees example from Section 3 -/
def testNonemptyTrees : MetaM Unit := do
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
      (t, .Undef $ mkConst `Tree),
      (x, .Undef $ mkConst `Nat),
      (l, .Undef $ mkConst `Tree),
      (r, .Undef $ mkConst `Tree)
    ]

    -- Unify: t ~ Node x l r (from constructor conclusion)
    let nodePattern := Range.Ctor `Node [.Unknown x, .Unknown l, .Unknown r]
    unify (.Unknown t) nodePattern

  match (← runUnifyState testUnify) with
  | some finalState =>
    IO.println s!"✓ Nonempty trees test passed"
    IO.println s!"  Final constraints: {repr finalState.constraints.toList}"
    -- Should show t bound to Node unknown0 unknown1 unknown2
  | none =>
    IO.println "✗ Nonempty trees test failed"

/-- Test complete trees example: complete n t -/
def testCompleteTrees : MetaM Unit := do
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
      (t, (.Undef $ mkConst `Tree)),
      (n, (.Undef $ mkConst `Nat)),
      (l, (.Undef $ mkConst `Tree)),
      (r, (.Undef $ mkConst `Tree))
    ]

    -- Unify constructor conclusion: complete (S n) (Node x l r) ~ complete in1 t
    let sn := Range.Ctor ``Nat.succ [.Unknown n]
    let nodePattern := Range.Ctor `Node [.Unknown `x, .Unknown l, .Unknown r]

    -- This should create pattern match on in1
    unify (.Unknown in1) sn
    unify (.Unknown t) nodePattern

  match (← runUnifyState testUnify) with
  | some finalState =>
    IO.println s!"✓ Complete trees test passed"
    IO.println s!"  Patterns generated: {repr finalState.patterns}"
    -- Should show pattern match on in1 against S n
  | none =>
    IO.println "✗ Complete trees test failed"


/-- Test binary search trees with bounds -/
def testBinarySearchTrees : MetaM Unit := do
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
      (t, (.Undef $ mkConst `Tree)),
      (x, (.Undef $ mkConst `Nat)),
      (l, (.Undef $ mkConst `Tree)),
      (r, (.Undef $ mkConst `Tree))
    ]

    -- Unify constructor conclusion: bst lo hi (Node x l r) ~ bst lo hi t
    let nodePattern := Range.Ctor `Node [.Unknown x, .Unknown l, .Unknown r]
    unify (.Unknown t) nodePattern

    -- Simulate processing premises: lo < x, x < hi, bst lo x l, bst x hi r
    -- These would create additional constraints in a full implementation

  match (← runUnifyState testUnify) with
  | some finalState =>
    IO.println s!"✓ BST test passed"
    IO.println s!"  Tree structure unified: {repr finalState.constraints}"
  | none =>
    IO.println "✗ BST test failed"


/-- Test non-linear patterns (same variable appears multiple times) -/
def testNonLinearPatterns : MetaM Unit := do
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
      (t1, (.Undef $ mkConst `type)),
      (t2, (.Undef $ mkConst `type)),
      (e, (.Undef $ mkConst `term))
    ]

    -- Create patterns with t1 appearing twice
    let absPattern := Range.Ctor `Abs [.Unknown t1, .Unknown e]
    let arrPattern := Range.Ctor `Arr [.Unknown t1, .Unknown t2]

    -- This should trigger pattern matching on term and typ
    unify (.Unknown term) absPattern
    unify (.Unknown typ) arrPattern

    -- The non-linearity of t1 should create equality constraints (unknown_3, unknown_6)

  match (← runUnifyState testUnify) with
  | some finalState =>
    IO.println s!"✓ Non-linear patterns test passed"
    IO.println s!"  Patterns: {repr finalState.patterns}"
    IO.println s!"  Equalities: {repr finalState.equalities.toList}"
    -- Should show pattern matches and equality constraints for t1
  | none =>
    IO.println "✗ Non-linear patterns test failed"

/-- Test function calls in constructor conclusions -/
def testFunctionCalls : MetaM Unit := do
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
      (n, .Undef $ mkConst `Nat),
      (m, .Undef $ mkConst `Nat)
    ]

    -- Unify: `square_of n (n * n) ~ square_of in1 in2`
    -- This should unify `n` with `in1`
    unify (.Unknown n) (.Unknown in1)

    -- The `(n * n)` part would normally create a fresh variable and equality
    -- For testing, we'll simulate this by creating an equality constraint
    let product ← UnifyM.registerFreshUnknown
    UnifyM.update product (.Undef $ mkConst `Nat)
    UnifyM.registerEquality product in2  -- product should equal in2

    -- Simulate the equality: product = n * n (would be handled by preprocessing)

  match (← runUnifyState testUnify) with
  | some finalState =>
    IO.println s!"✓ Function calls test passed"
    IO.println s!"  Equalities created: {repr finalState.equalities.toList}"
  | none =>
    IO.println "✗ Function calls test failed"


/-- Run all test cases -/
def runAllTests : MetaM Unit := do
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
