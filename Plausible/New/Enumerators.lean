import Plausible.New.LazyList
open LazyList


abbrev Enumerator (α : Type) := Nat → LazyList α

-- def returnEnum (x : α) : Enumerator α :=
--   fun _ =>

-- instance : Monad Enumerator where
