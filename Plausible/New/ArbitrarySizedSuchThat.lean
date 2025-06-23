import Plausible.Gen
import Plausible.New.OptionTGen
open Plausible

/-- Sized generators of type `α` such that `P : α -> Prop` holds for all generated values.
    Note that these generators may fail, which is why they have type `OptionT Gen α`. -/
class ArbitrarySizedSuchThat (α : Type) (P : α → Prop) where
  arbitrarySizedST : Nat → OptionT Gen α

/-- Generators of type `α` such that `P : α -> Prop` holds for all generated values.
    Note that these generators may fail, which is why they have type `OptionT Gen α`. -/
class ArbitrarySuchThat (α : Type) (P : α → Prop) where
  arbitraryST : OptionT Gen α

/-- Every `ArbitrarySizedSuchThat` instance can be automatically given a `ArbitrarySuchThat` instance
    using the `OptionTGen.sized` combinator -/
instance [ArbitrarySizedSuchThat α P] : ArbitrarySuchThat α P where
  arbitraryST := OptionTGen.sized (ArbitrarySizedSuchThat.arbitrarySizedST P)
