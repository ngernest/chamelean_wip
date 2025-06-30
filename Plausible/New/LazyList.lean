
-- Adapted from QuickChick source code
-- https://github.com/QuickChick/QuickChick/blob/master/src/LazyList.v

/-- Lazy Lists are implemented by thunking the computation for the tail of a cons-cell. -/
inductive LazyList (α : Type u) where
  | lnil
  | lcons : α → Thunk (LazyList α) → LazyList α
deriving Inhabited

namespace LazyList

/-- Converts a Lazy List to an ordinary list by forcing all the embedded thunks -/
def toList : LazyList α → List α
  | lnil => []
  | .lcons x xs => x :: xs.get.toList

/-- We pretty-print `LazyList`s by converting them to ordinary lists
    (forcing all the thunks) & pretty-printing the resultant list. -/
instance [Repr α] : Repr (LazyList α) where
  reprPrec l _ := repr l.toList

/-- Retrieves a prefix of the `LazyList` (only the thunks in the prefix are evaluated) -/
def take (n : Nat) (l : LazyList α) : LazyList α :=
  match n with
  | .zero => lnil
  | .succ n' =>
    match l with
    | lnil => lnil
    | .lcons x xs => .lcons x (take n' xs.get)

/-- Appends two `LazyLists` together
    (Note: the body of delayed does not need to be an explicit call to `Thunk.mk` because
    Lean automatically coerces any `e : α` into `Thunk.mk (fun () => e) : Thunk α`.) -/
def append (xs : LazyList α) (ys : LazyList α) : LazyList α :=
  match xs with
  | lnil => ys
  | .lcons x xs' => .lcons x (append xs'.get ys)

/-- `observe tag i` uses `dbg_trace` to emit a trace of the variable
    associated with `tag` -/
def observe (tag : String) (i : Fin n) : Nat :=
  dbg_trace "{tag}: {i.val}"
  i.val

/-- Maps a function over a LazyList -/
def mapLazyList (f : α → β) (l : LazyList α) : LazyList β :=
  match l with
  | lnil => lnil
  | .lcons x xs => .lcons (f x) (mapLazyList f xs.get)

/-- `Functor` instance for `LazyList` -/
instance : Functor LazyList where
  map := mapLazyList

/-- Creates a singleton LazyList -/
def pureLazyList (x : α) : LazyList α :=
  LazyList.lcons x $ Thunk.mk (fun _ => lnil)

/-- Alias for `pureLazyList` -/
def singleton (x : α) : LazyList α :=
  pureLazyList x

/-- Flattens a `LazyList (LazyList α)` into a `LazyList α`  -/
def concat (l : LazyList (LazyList α)) : LazyList α :=
  match l with
  | lnil => lnil
  | .lcons x l' => append x (concat l'.get)

/-- Bind for `LazyList`s is just `concatMap` (same as the list monad) -/
def bindLazyList (l : LazyList α) (f : α → LazyList β) : LazyList β :=
  concat (f <$> l)

/-- `Monad` instance for `LazyList` -/
instance : Monad LazyList where
  pure := pureLazyList
  bind := bindLazyList

/-- `Applicative` instance for `LazyList` -/
instance : Applicative LazyList where
  pure := pureLazyList

/-- `Alternative` instance for `LazyList`s, where `xs <|> ys` is just `LazyList` append -/
instance : Alternative LazyList where
  failure := lnil
  orElse xs f := append xs (f ())

/-- Creates a lazy list by repeatedly applying a function `s` to generate a sequence of elements -/
def lazySeq (s : α → α) (lo : α) (len : Nat) : LazyList α :=
  match len with
  | .zero => lnil
  | .succ len' => .lcons lo (lazySeq s (s lo) len')

end LazyList
