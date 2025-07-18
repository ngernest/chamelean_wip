import Lean
import Batteries
open Lean

/-- A source is the thing we wish to check/generate/enumerate -/
inductive Source where
  | NonRec : Expr → Source
  | Rec : String → List Expr → Source

/-- Producers are either enumerators or generators -/
inductive ProducerSort : Type where
  | Enumerator
  | Generator

inductive ScheduleSort : Type where
  /-- tuple of produced outputs from conclusion of constructor -/
  | ProducerSchedule : Bool → ProducerSort → Expr → ScheduleSort

  /-- checkers need not bother with conclusion of constructor,
      only hypotheses need be checked and conclusion of constructor follows-/
  | CheckerSchedule

/-- A single step in a generator schedule -/
inductive ScheduleStep where
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

/-- A schedule is a pair consisting of an ordered list of `ScheduleStep`s,
    and the sort of schedule we're dealing with -/
abbrev Schedule := (List ScheduleStep) × ScheduleSort


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
