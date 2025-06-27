
import Lean
import Plausible.IR.Prelude

open Lean Meta
open Plausible.IR

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
