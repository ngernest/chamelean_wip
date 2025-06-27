
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

/-- We pretty-print `LazyList`s by converting them to ordinary lists
    (forcing all the thunks) & pretty-printing the resultant list. -/
instance [Repr α] : Repr (LazyList α) where
  reprPrec l _ := repr l.toList

-- Many operations on lazy lists can be implemented without forcing the embedded thunks,
-- instead building up further thunks.

/-- Retrieves a prefix of the `LazyList` (only the thunks in the prefix are evaluated) -/
def take : Nat → LazyList α → LazyList α
  | 0, _ => .nil
  | _, .nil => .nil
  | n + 1, .cons x xs => .cons x $ .delayed (take n xs)
  | n + 1, .delayed xs => .delayed $ take (n + 1) xs.get

/-- Creates a `LazyList` from a function `f` -/
def ofFn (f : Fin n → α) : LazyList α :=
  Fin.foldr n (fun i xs => .delayed $ LazyList.cons (f i) xs) (init := .nil)

/-- Appends two `LazyLists` together
    (Note: the body of delayed does not need to be an explicit call to `Thunk.mk` because
    Lean automatically coerces any `e : α` into `Thunk.mk (fun () => e) : Thunk α`.) -/
def append (xs ys : LazyList α) : LazyList α :=
  .delayed $
    match xs with
    | .nil => ys
    | .cons x xs' => LazyList.cons x (append xs' ys)
    | .delayed xs' => append xs'.get ys

/-- `observe tag i` uses `dbg_trace` to emit a trace of the variable
    associated with `tag` -/
def observe (tag : String) (i : Fin n) : Nat :=
  dbg_trace "{tag}: {i.val}"
  i.val

def xs := LazyList.ofFn (n := 3) (observe "xs")
def ys := LazyList.ofFn (n := 3) (observe "ys")

/-- Maps a function over a LazyList -/
def mapLazyList (f : α → β) (l : LazyList α) : LazyList β :=
  match l with
  | .nil => .nil
  | .cons x xs => .cons (f x) (mapLazyList f xs)
  | .delayed xs => .delayed $ mapLazyList f xs.get

/-- `Functor` instance for `LazyList` -/
instance : Functor LazyList where
  map := mapLazyList

/-- Creates a singleton LazyList -/
def pureLazyList (x : α) : LazyList α :=
  .cons x .nil

/-- Flattens a `LazyList (LazyList α)` into a `LazyList α`  -/
def concatLazyList (l : LazyList (LazyList α)) : LazyList α :=
  match l with
  | .nil => .nil
  | .cons x l' => append x (concatLazyList l')
  | .delayed xss => concatLazyList xss.get

/-- Bind for `LazyList`s is just `concatMap` (same as the list monad) -/
def bindLazyList (l : LazyList α) (f : α → LazyList β) : LazyList β :=
  concatLazyList (f <$> l)

/-- `Monad` instance for `LazyList` -/
instance : Monad LazyList where
  pure := pureLazyList
  bind := bindLazyList

/-- `Applicative` instance for `LazyList` -/
instance : Applicative LazyList where
  pure := pureLazyList

end LazyList
