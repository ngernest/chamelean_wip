import Plausible.Gen
import Plausible.New.OptionTGen
open Plausible

/-- Sized generators of type `α` such that `P : α -> Prop` holds for all generated values.
    Note that these generators may fail, which is why they have type `OptionT Gen α`. -/
class GenSizedSuchThat (α : Type u) (P : α → Prop) where
  genSizedST : Nat → OptionT Gen α

/-- Generators of type `α` such that `P : α -> Prop` holds for all generated values.
    Note that these generators may fail, which is why they have type `OptionT Gen α`. -/
class GenSuchThat (α : Type u) (P : α → Prop) where
  genST : OptionT Gen α

/-- Every `GenSizedSuchThat` instance can be automatically given a `GenSuchThat` instance
    using the `OptionTGen.sized` combinator -/
instance [GenSizedSuchThat α P] : GenSuchThat α P where
  genST := OptionTGen.sized (GenSizedSuchThat.genSizedST P)
