
import Lean
import Plausible.IR.Prelude
import Batteries.Data.List.Basic

open Lean Meta
open Plausible.IR

/-- Determines if an instance of the typeclass `className` exists for a particular `type`
    represented as an `Expr`. Under the hood, this tries to synthesize an instance of the typeclass for the type.

    Example:
    ```
    #eval hasInstance `Repr (Expr.const `Nat []) -- returns true
    ```
-/
def hasInstance (className : Name) (type : Expr) : MetaM Bool := do
  let classType ← mkAppM className #[type]
  Option.isSome <$> synthInstance? classType


/-- Determines if a constructor for an inductive relation is *recursive*
    (i.e. the constructor's type mentions the inductive relation)
    - Note: this function only considers constructors with arrow types -/
def isConstructorRecursive (inductiveName : Name) (ctorName : Name) : MetaM Bool := do
  let ctorInfo ← getConstInfo ctorName
  let ctorType := ctorInfo.type

  let (_, _, type_exprs_in_arrow_type) ← decomposeType ctorType
  match splitLast? type_exprs_in_arrow_type with
  | some (hypotheses, _conclusion) =>
    for hyp in hypotheses do
      if hyp.getAppFn.constName == inductiveName then
        return true
    return false
  | none => throwError "constructors with non-arrow types are not-considered to be recursive"

/-- `replicateM n act` performs the action `act` for `n` times, returning a list of results. -/
def replicateM [Monad m] (n : Nat) (action : m α) : m (List α) :=
  match n with
  | 0 => pure []
  | n + 1 => do
    let x ← action
    let xs ← replicateM n action
    pure (x :: xs)

/-- Converts a list of options to an optional list
    (akin to Haskell's `sequence`) -/
def List.sequence (xs : List (Option α)) : Option (List α) :=
  List.traverse id xs

/-- `ToMessageData` instance for pretty-printing `ConstructorVal`s -/
instance : ToMessageData ConstructorVal where
  toMessageData ctorVal :=
    let fields := [
      m!"name := {ctorVal.name}",
      m!"levelParams := {ctorVal.levelParams}",
      m!"type := {ctorVal.type}",
      m!"induct := {ctorVal.induct}",
      m!"cidx := {ctorVal.cidx}",
      m!"numParams := {ctorVal.numParams}",
      m!"numFields := {ctorVal.numFields}",
      m!"isUnsafe := {ctorVal.isUnsafe}"
    ]
    .bracket "{" (.ofList fields) "}"
