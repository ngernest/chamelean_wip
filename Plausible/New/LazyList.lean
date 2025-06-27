
-- Adapted from section 18.19.3 of the Lean Language Reference
-- https://lean-lang.org/doc/reference/latest/Basic-Types/Lazy-Computations/#Thunk-coercions

/-- Lazy lists are lists that may contain thunks.
    The `delayed` constructor causes part of the list to be computed on demand. -/
inductive LazyList (α : Type u) where
  | nil
  | cons : α → LazyList α → LazyList α
  | delayed : Thunk (LazyList α) → LazyList α
deriving Inhabited

namespace LazyList

/-- Converts a Lazy List to an ordinary list by forcing all the embedded thunks -/
def toList : LazyList α → List α
  | .nil => []
  | .cons x xs => x :: xs.toList
  | .delayed xs => xs.get.toList

/-- Retrieves a prefix of the `LazyList` (only the thunks in the prefix are evaluated) -/
def take : Nat → LazyList α → LazyList α
  | 0, _ => .nil
  | _, .nil => .nil
  | n + 1, .cons x xs => .cons x $ .delayed (take n xs)
  | n + 1, .delayed xs => .delayed $ take (n + 1) xs.get

/-- Creates a `LazyList` from a function `f` -/
def ofFn (f : Fin n → α) : LazyList α :=
  Fin.foldr n (init := .nil) (fun i xs =>
    .delayed $ LazyList.cons (f i) xs)

/-- Appends two `LazyLists` together
    (Note: the body of delayed does not need to be an explicit call to `Thunk.mk` because
    Lean automatically coerces any `e : α` into `Thunk.mk (fun () => e) : Thunk α`.) -/
def append (xs ys : LazyList α) : LazyList α :=
  .delayed $
    match xs with
    | .nil => ys
    | .cons x xs' => LazyList.cons x (append xs' ys)
    | .delayed xs' => append xs'.get ys

def observe (tag : String) (i : Fin n) : Nat :=
  dbg_trace "{tag}: {i.val}"
  i.val

def xs := LazyList.ofFn (n := 3) (observe "xs")
def ys := LazyList.ofFn (n := 3) (observe "ys")


end LazyList
