import Plausible.IR.Example

import Plausible.Gen
import Plausible.Sampleable
open Plausible

-- Note: this file has been deprecated.
-- Prefer `OptionT Gen α` over `Gen (Option α)` (the former is more expressive).

------------------------
-- The GenOption monad
------------------------

/-- Type alias for Generators that produce a value wrapped in a `Option`
    (i.e. generators that may fail, i.e. because they ran out of fuel or because they failed to produce an inhabitant of `α`) -/
abbrev GenOption (α : Type) := Gen (Option α)

/-- Pure: wrap a value in Some and lift to Gen -/
def genOptionPure {α : Type} (a : α) : Gen (Option α) :=
  pure (some a)

/-- Bind: extract the value if Some, otherwise propagate None -/
def genOptionBind {α β : Type} (g : GenOption α) (f : α → GenOption β) : Gen (Option β) := do
  let a_opt ← g
  match a_opt with
  | none => pure none
  | some a => f a

/-- `Monad` instance for `GenOption` -/
instance : Monad GenOption where
  pure := genOptionPure
  bind := genOptionBind

/-- Converts a `GenOption α` into a `GenOption β` using the function `f` -/
def genOptionMap {α β : Type} (f : α → β) (ga : GenOption α) : GenOption β :=
  ga >>= (pure ∘ f)

/-- `Functor` instance for `GenOption` -/
instance : Functor GenOption where
  map := genOptionMap

/-- Lifts a `Gen α` into a `Gen (Option α)`.
   (this allow us to use `Gen α` computations in places where `GenOption α` is expected) -/
def liftGenOption {α : Type} (g : Gen α) : Gen (Option α) :=
  g >>= (fun x => pure (some x))
