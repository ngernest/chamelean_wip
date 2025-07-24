import Lean
import Batteries
import Plausible.GeneratingGoodGenerators.UnificationMonad

open Lean

/-- A `HypothesisExpr` is a datatype representing a hypothesis for a
    constructor of an inductive relation, consisting of a constructor name
    applied to some list of arguments, each of which are `ConstructorExpr`s -/
abbrev HypothesisExpr := Name × List ConstructorExpr

/-- A source is the thing we wish to check/generate/enumerate -/
inductive Source
  | NonRec : HypothesisExpr → Source
  | Rec : Name → List ConstructorExpr → Source
  deriving Repr

/-- Producers are either enumerators or generators -/
inductive ProducerSort
  | Enumerator
  | Generator
  deriving Repr

/-- The sort of function we are deriving based on an inductive relation:
    determines whether we are deriving a (constrained) generator, enumerator or a checker. -/
inductive DeriveSort
  | Generator
  | Enumerator
  | Checker
  deriving Repr, BEq

inductive ScheduleSort
  /-- tuple of produced outputs from conclusion of constructor -/
  | ProducerSchedule : Bool → ProducerSort → Expr → ScheduleSort

  /-- checkers need not bother with conclusion of constructor,
      only hypotheses need be checked and conclusion of constructor follows-/
  | CheckerSchedule

  deriving Repr


/-- A single step in a generator schedule -/
inductive ScheduleStep
  /-- Unconstrained generation -/
  | Unconstrained : String → Source → ProducerSort → ScheduleStep

  /-- Generate a value such that a predicate is satisfied -/
  | SuchThat : List (String × Expr) → Source → ProducerSort → ScheduleStep

  /-- Check whether some proposition holds
     (the bool is the desired truth value of the proposition we're checking) -/
  | Check : Source → Bool → ScheduleStep

  /-- Used when you decompose a constructor constrained arg into a
    fresh variable followed by a pattern match -/
  | Match : Source → Expr → ScheduleStep

  deriving Repr

/-- A schedule is a pair consisting of an ordered list of `ScheduleStep`s,
    and the sort of schedule we're dealing with (the latter is the "conclusion" of the schedule) -/
abbrev Schedule := List ScheduleStep × ScheduleSort


/-- Each `ScheduleStep` is associated with a `Density`, which represents a failure mode of a generator -/
inductive Density
  /-- Invokes a call to a checker -/
  | Checking

  /-- A call to `ArbitrarySuchThat`, followed by a pattern-match on the generated value
      (this happens when we want the output of the generator to have a certain shape) -/
  | Backtracking

  /-- a call to `ArbitrarySuchThat` ??? -/
  | Partial

  /-- Unconstrained generation, i.e. calls to `arbitrary` -/
  | Total
  deriving Repr, BEq
