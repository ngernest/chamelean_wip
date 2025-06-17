import Plausible.New.OptionTGen

/-- Generators of type [α] such that [P : α -> Prop] holds for all generated values -/
class GenSizedSuchThat (α : Type u) (P : α → Prop) where
  genSizedST : Nat → OptionT Gen α
