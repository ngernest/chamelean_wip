import Plausible.Chamelean.LazyList
import Plausible.Chamelean.Utils

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
  fun _ => .lnil

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

-- Some simple `Enum` instances

/-- `Enum` instance for `Bool` -/
instance : Enum Bool where
  enum := pureEnum false <|> pureEnum true

/-- `Enum` instance for `Nat` -/
instance : Enum Nat where
  enum := fun n => lazySeq .succ 0 (n + 1)

/-- `Enum` instance for `Option`s -/
instance [Enum α] : Enum (Option α) where
  enum := fun n =>
    (return none) <|> (some <$> Enum.enum n)

/-- `Enum` instances for pairs -/
instance [Enum α] [Enum β] : Enum (α × β) where
  enum := fun n => do
    let a ← Enum.enum n
    let b ← Enum.enum n
    pure (a, b)

/-- `Enum` instances for sums -/
instance [Enum α] [Enum β] : Enum (α ⊕ β) where
  enum := fun n =>
    (Enum.enum n >>= pure ∘ Sum.inl) <|> (Enum.enum n >>= pure ∘ Sum.inr)

/-- Helper function: enumerates lists with a certain `budget` that is
    halved during each recursive calls -/
def enumListsWithBudget [Enum α] (budget : Nat) : LazyList (List α) :=
  let empty := LazyList.singleton []
  match budget with
  | 0 => empty
  | .succ budget' =>
    let non_empty := do
      let hd ← Enum.enum budget
      let tl ← enumListsWithBudget (budget' / 2)
      pure (hd :: tl)
    empty <|> non_empty

/-- `Enum` instances for lists -/
instance [Enum α] : Enum (List α) where
  enum := sizedEnum (fun size => (fun _ => enumListsWithBudget size))

/-- Enumerates all printable ASCII characters (codepoint 32 - 95) -/
def enumPrintableASCII (size : Nat) : LazyList Char :=
  lazySeq (fun c => Char.ofNat (c.toNat + 1)) (Char.ofNat 32) (min size 95)

/-- `Enum` instance for ASCII-printable `Char`s -/
instance : Enum Char where
  enum := enumPrintableASCII

/-- `Enum` instance for `String`s containing ASCII-printable characters -/
instance : Enum String where
  enum := List.asString <$> (Enum.enum : Enumerator (List Char))

/-- Produces a `LazyList` containing all `Int`s in-between
    `lo` and `hi` (inclusive) in ascending order -/
def lazyListNatRange (lo : Nat) (hi : Nat) : LazyList Nat :=
  lazySeq .succ lo (.succ (hi - lo))

/-- Enumerates all `Nat`s in-between `lo` and `hi` (inclusive)
    in ascending order -/
def enumNatRange (lo : Nat) (hi : Nat) : Enumerator Nat :=
  fun _ => lazyListNatRange lo hi

/-- Produces a `LazyList` containing all `Int`s in-between
    `lo` and `hi` (inclusive) in ascending order -/
def lazyListIntRange (lo : Int) (hi : Int) : LazyList Int :=
  lazySeq (. + 1) lo (Int.toNat (hi - lo + 1))

/-- `Enum` instance for `Int` (enumerates all `int`s between `-size` and `size` inclusive) -/
instance : Enum Int where
  enum := fun size =>
    let n := Int.ofNat size
    lazyListIntRange (-n) n

/-- `Enum` instance for `Fin n` where `n > 0`
  (enumerates all `Nat`s from 0 to `n - 1` inclusive) -/
instance [NeZero n] : Enum (Fin n) where
  enum := fun _ =>
    (Fin.ofNat n) <$> lazyListNatRange 0 (n - 1)

/-- `Enum` instance for `BitVec w`
    (uses the `Enum` instance for `Fin (2 ^ w)`, since bitvectors
    are represented using `Fin (2 ^ w)` under the hood) -/
instance : Enum (BitVec w) where
  enum := BitVec.ofFin <$> (Enum.enum : Enumerator (Fin (2 ^ w)))


-- Sampling from enumerators

/-- Returns the list of elements produced by the enumerator
    associated with the `Enum` instance for a type,
    using `size` as the size parameter for the enumerator.
    To invoke this function, you will need to specify what type `α` is,
    for example by doing `runEnum (α := Nat) 10`. -/
def runEnum [Enum α] (size : Nat) : IO (List α) :=
  return (LazyList.toList $ Enum.enum size)

/-- Samples from an `OptionT Enumerator` enumerator that is parameterized by its `size`,
    returning the enumerated list of `Option α` values in the `IO` monad
    - TODO: investigate why there are many duplicate values in the resultant `LazyList` -/
def runSizedEnum (sizedEnum : Nat → OptionT Enumerator α) (size : Nat) : IO (List (Option α)) :=
  return (LazyList.toList $ (sizedEnum size) size)
