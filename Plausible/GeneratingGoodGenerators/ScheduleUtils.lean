import Lean
import Plausible.IR.Examples

open Plausible.IR

open Lean Meta

/-- Extracts all the unique variables that appear in a hypothesis of an inductive relation constructor
    (this looks underneath constructor applications).

    For example, given `typing Γ (type.Abs τ1 e) (type.Fun τ1 τ2)`,
    this function returns `[Γ, τ1, e, τ2]`.
 -/
partial def extractVariablesInHypothesis (term : TSyntax `term) : MetaM (List Name) :=
  match term with
  | `($id:ident) => return [id.getId.eraseMacroScopes]
  | `($_:ident $args:term*)
  | `(($_:ident $args*)) => do
    let foo ← args.toList.flatMapM extractVariablesInHypothesis
    return (List.eraseDups foo)
  | _ => return []


#eval show MetaM _ from do
  extractVariablesInHypothesis (← `(typing Γ (type.Abs τ1 e) (type.Fun τ1 τ2)))
