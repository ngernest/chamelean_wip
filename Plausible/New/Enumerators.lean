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

/-- The degenerate enumerator which enumerates nothing (the empty `LazyList`) -/
def failEnum : Enumerator α :=
  fun _ => LazyList.nil

/-- `Alternative` instance for `Enumerator`s.
    Note:
    - `e1 <|> e2` is not fair and is biased towards `e1`, i.e. all elements of `e1` will
      appear in the resultant enumeration before the first element of `e2`.
    - Defining a fair instance of `Alternative` requires defining an interleave operation
      on the resultant lists (see "A Completely Unique Account of Enumeration", ICFP '22),
      however it is unclear how to define an interleave operation on *LazyLists* while
      convincing Lean's termination checker to accept the definition (essentially, the
      difficulty lies in proving that forcing the thunked tail of a `LazyList` doesn't
      increase the size of the overall `LazyList`). -/
instance : Alternative Enumerator where
  failure := failEnum
  orElse e1 e2 := fun n => (e1 n) <|> (e2 () n)

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


/-- `Enum` instance for `Bool` -/
instance : Enum Bool where
  enum := pureEnum false <|> pureEnum true
