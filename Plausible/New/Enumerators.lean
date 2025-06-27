import Plausible.New.LazyList
open LazyList

/-- An enumerator is a function from `Nat` to `LazyList α`, where the `Nat`
    serves an upper bound for the enumeration process, i.e. the LazyList returned
    contains all inhabitants of `α` up to the given size. -/
abbrev Enumerator (α : Type) := Nat → LazyList α

/-- `pure x` constructs a trivial enumerator which produces a singleton `LazyList` containing `x` -/
def pureEnum (x : α) : Enumerator α :=
  fun _ => pureLazyList x

/-- Monadic-bind for enumerators -/
def bindEnum (enum : Enumerator α) (k : α → Enumerator β) : Enumerator β :=
  fun (n : Nat) => do
    let x ← enum n
    (k x) n

/-- `Monad` instance for `Enumerator`s -/
instance : Monad Enumerator where
  pure := pureEnum
  bind := bindEnum

/-- `sizedEnum f` constructs an enumerator that depends on `size` parameter -/
def sizedEnum (f : Nat → Enumerator α) : Enumerator α :=
  fun (n : Nat) => (f n) n

/-- The `Enum` typeclass describes types that have an associated `Enumerator` -/
class Enum (α : Type) where
  enum : Enumerator α

/-- The `EnumSized` typeclass describes enumerators that have an
    additional `Nat` parameter to bound their recursion depth. -/
class EnumSized (α : Type) where
  enumSized : Nat → Enumerator α

/-- Sized enumerators of type `α` such that `P : α -> Prop` holds for all enumerated values.
    Note that these enumerators may fail, which is why they have type `OptionT Enumerator α`. -/
class EnumSizedSuchThat (α : Type) (P : α → Prop) where
  enumSizedST : Nat → OptionT Enumerator α

/-- Enumerators of type `α` such that `P : α -> Prop` holds for all generated values.
    Note that these enumerators may fail, which is why they have type `OptionT Enumerator α`. -/
class EnumSuchThat (α : Type) (P : α → Prop) where
  enumST : OptionT Enumerator α

/-- Every `EnumSized` instance gives rise to an `Enum` instance -/
instance [EnumSized α] : Enum α where
  enum := sizedEnum EnumSized.enumSized

/-- Every `EnumSizedSuchThat` instance gives rise to an `EnumSuchThat` instance -/
instance [EnumSizedSuchThat α P] : EnumSuchThat α P where
  enumST := sizedEnum (EnumSizedSuchThat.enumSizedST P)
