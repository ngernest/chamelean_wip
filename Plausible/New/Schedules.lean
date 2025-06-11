import Lean
open Lean

/-- A source is the thing we wish to check/generate/enumerate -/
inductive Source where
  | NonRec : Expr → Source
  | Rec : String → List Expr → Source

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

/-- Producers are either enumerators or generators -/
inductive ProducerSort where
  | Enumerator
  | Generator

inductive ScheduleSort where

  /-- tuple of produced outputs from conclusion of constructor -/
  | ProducerSchedule : Bool → ProducerSort → Expr → ScheduleSort

  /-- checkers need not bother with conclusion of constructor,
      only hypotheses need be checked and conclusion of constructor follows-/
  | CheckerSchedule

/-- A schedule is a pair consisting of an ordered list of `ScheduleStep`s,
    and the sort of schedule we're dealing with -/
abbrev Schedule := (List ScheduleStep) × ScheduleSort
