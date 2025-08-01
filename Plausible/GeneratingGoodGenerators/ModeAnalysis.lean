import Lean
import Plausible.GeneratingGoodGenerators.UnificationMonad
import Plausible.New.TSyntaxCombinators

open Lean Meta

/-- Corresponds to the `range_mode` type in the QuickChick code -/
inductive RangeMode
  /-- Inputs that are `Fixed` at runtime (i.e. top-level arguments to the generator),
      corresponds to `Range.Fixed` -/
  | ModeFixed

  /-- Corresponds to `u ↦ Range.Undef ty` in the `constraints` map
      (this means we need to generate a value `u` of type `ty`) -/
  | ModeUndefUnknown (u : Unknown) (ty : Expr)

  /-- A partially instantiated range which needs pattern matching -/
  | ModePartlyDef (pattern : Pattern)

  deriving Repr, Inhabited

/-- Notion of *compatibility* from Computing Correctly (section 4), used to handle situations
    when a hypothesis is a recursive occurrence of the inductive relation we're targeting -/
inductive Compatibility
  /-- Every argument to the inductive relation in the hypothesis
      is compatible with its corresponding argument in the top-level inductive relation we're targeting
      (no variables need additional instantiation)

      - For `Compatible`, we can just make a recursive call to the producer function -/
  | Compatible

  /-- There exists some incompatible argument that is more instantiated than expected.
      This only happens when deriving a producer, because all arguments need to be
      instantiated when deriving a checker. For this case, we just invoke a checker
      (via the `DecOpt` instance for the inductive relation). -/
  | Incompatible

  /-- Every argument to the inductive relation in the hypothesis is compatible with
      its corresponding arugment in the top-level inductive relation,
      but some variables need additional instantiation.

      For `PartCompatible`, we make an `arbitrarySuchThat` call (a call to a constrained prdoucer). -/
  | PartCompatible

  /-- Every argument to the inductive relation in the hypothesis is compatible with
      its corresponding arugment in the top-level inductive relation,
      but some variables need additional instantiation.

      For `InstCompatible`, we produce the variable and make a recursive call to
      the checker/producer function we're deriving. -/
  | InstCompatible

  deriving BEq, Repr, Inhabited

/-- Determines whether a `mode` is compatible given a boolean indicating
    whether a typeclass instance exists for a particular type constructor
    (corresponds to `compatible` in the OCaml code) -/
def compatible (m : RangeMode) (b : Bool) : Compatibility :=
  match m, b with
  | .ModeFixed, false => .Compatible
  | .ModeUndefUnknown _ _, false => .InstCompatible
  | .ModePartlyDef _, false => .InstCompatible
  | .ModeFixed, true => .Incompatible
  | .ModeUndefUnknown _ _, true => .Compatible
  | .ModePartlyDef _, true => .PartCompatible

/-- `convertToPattern parent r` converts the `Range` `r` to a `Pattern`,
     where `parent` is the `Unknown`
     - Corresponds to `convert_to_pat` in the QuickChick code -/
partial def convertToPattern (parent : Unknown) (r : Range) : UnifyM Pattern :=
  match r with
  | .Ctor c rs => do
    let ctorArgPatterns ← rs.mapM (convertToPattern `unusedParameter)
    return .CtorPattern c ctorArgPatterns
  | .Unknown u =>
    UnifyM.withConstraints $ fun k => do
      let r ← UnifyM.findCorrespondingRange k u
      convertToPattern u r
  | .Fixed => do
    let u ← UnifyM.registerFreshUnknown
    UnifyM.registerEquality u parent
    return .UnknownPattern u
  | .Undef _ =>
    UnifyM.withUnknowns $ fun unknowns =>
      if unknowns.any (fun u => u == parent) then do
        let u ← UnifyM.registerFreshUnknown
        UnifyM.registerEquality u parent
        return .UnknownPattern u
      else do
        UnifyM.insertUnknown parent
        return .UnknownPattern parent

mutual
  /-- Instantiates a single range `r`, taking in a continuation which receives the isntantiated range to produce a term
      - Corresponds to `instantiate_range_cont` in the QuickChick codebase -/
  partial def instantiateRangeCPS (parent : Unknown) (r : Range) (cont : Range → UnifyM (TSyntax `term)) : UnifyM (TSyntax `term) :=
    match r with
    | .Ctor c rs =>
      instantiateTopLevelRangesCPS rs [] (fun rs' => cont (.Ctor c rs'))
    | .Undef _ => do
      -- TODO: investigate how to create the let-bind expression here
      UnifyM.fixRangeHandleUnknownChains parent
      cont (.Unknown parent)
    | .Unknown u => do
      UnifyM.withConstraints (fun k => do
        let r ← UnifyM.findCorrespondingRange k u
        instantiateRangeCPS u r cont
      )
    | .Fixed => cont (.Unknown parent)

  /-- Variant of `instantiateRangeCPS` that operates on a list of `Range`s at once
      - Corresponds to `instantiate_toplevel_ranges_cont` in the QuickChick codebase
   -/
  partial def instantiateTopLevelRangesCPS (rs : List Range) (acc : List Range) (cont : List Range → UnifyM (TSyntax `term)) : UnifyM (TSyntax `term) :=
    match rs with
    | [] => cont (List.reverse acc)
    | r :: rs' => instantiateRangeCPS `unusedParameter r (fun range => instantiateTopLevelRangesCPS rs' (range::acc) cont)
end


/-- Handles the case where a `Range` is partially instantiated:
    When this happens, we convert the range to a pattern, then wrap it in `ModePartlyDef`
    - Corresponds to `handle_partial` in the QuickChick code -/
def handlePartial (r : Range) : UnifyM RangeMode :=
  RangeMode.ModePartlyDef <$> convertToPattern `unusedParameter r

/-- `modeAnalyze k r` converts a `Range` `r` to a `RangeMode`
     based on the information in the `UnknownMap` `k`
     - corresponds to `mode_analyze` in the QuickChick codebase -/
partial def modeAnalyze (k : UnknownMap) (r : Range) : UnifyM RangeMode := do
  if (← UnifyM.hasFixedRange k r)
    then return .ModeFixed
  else
    match r with
    | .Unknown u =>
      -- Helper function for following a chain of unknowns in the `constraints` map
      let rec followUnknownChain (u : Unknown) : UnifyM RangeMode := do
        let range ← UnifyM.findCorrespondingRange k u
        match range with
        | .Undef ty => return .ModeUndefUnknown u ty
        | .Unknown u' => followUnknownChain u'
        | _ => handlePartial range -- Handle partially defined case
      followUnknownChain u
    | .Fixed => return .ModeFixed
    | .Ctor _ _ => handlePartial r
    | .Undef ty => do
      let u ← UnifyM.registerFreshUnknown
      return .ModeUndefUnknown u ty

/-- Compatibility scores (corresponds to `mode_score` in the OCaml code) -/
structure CompatibilityScores where
  numCompatible : Nat
  numInstCompatible : Nat
  numIncompatible : Nat
  numPartCompatible : Nat
  deriving Repr

-- corresponds to `mode_score` in the OCaml code
def modeScore (bs : List Bool) (ms : List RangeMode) : CompatibilityScores :=
  let compatibilityResults := (Function.uncurry compatible) <$> List.zip ms bs
  { numCompatible := List.count .Compatible compatibilityResults,
    numInstCompatible := List.count .InstCompatible compatibilityResults,
    numIncompatible := List.count .Incompatible compatibilityResults,
    numPartCompatible := List.count .PartCompatible compatibilityResults }
