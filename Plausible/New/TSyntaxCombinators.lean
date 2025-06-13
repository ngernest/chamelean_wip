import Lean
open Lean Elab Command Meta Term Parser

/-- `mkLetBind lhs rhsTerms` constructs a monadic let-bind expression of the form
    `let lhs ← e0 e1 … en`, where `rhsTerms := #[e0, e1, …, en]`.
    - Note: `rhsTerms` cannot be empty, otherwise this function throws an exception -/
def mkLetBind (lhs : Ident) (rhsTerms : TSyntaxArray `term) : MetaM (TSyntax `doElem) := do
  let rhsList := rhsTerms.toList
  match rhsList with
  | f :: args =>
    let argTerms := args.toArray
    `(doElem| let $lhs:term ← $f:term $argTerms* )
  | [] => throwError "rhsTerms can't be empty"

/-- Constructs a Lean monadic `do` block out of an array of `doSeq`s
    (expressions that appear in the `do` block) -/
def mkDoBlock (doElems : TSyntaxArray `doElem) : MetaM (TSyntax `term) := do
  `(do $[$doElems:doElem]*)

/-- `mkIfExprWithNaryAnd predicates trueBranch elseBranch` creates an if-expression
    `if (p1 && … && pn) then $trueBranch else $elseBranch`, where `predicates := #[p1, …, pn]`
    - Note: if `predicates` is empty, the expression created is `if True then $trueBranch else $elseBranch` -/
def mkIfExprWithNaryAnd (predicates : Array Term)
  (trueBranch : TSyntax `doElem) (elseBranch : TSyntax `doElem) : MetaM (TSyntax `doElem) := do
  let condition ←
    match predicates.toList with
    | [] => `(True)
    | [p] => pure p
    | p :: ps =>
      List.foldlM (fun acc pred => `($acc && $pred)) (init := p) ps
  `(doElem| if $condition then $trueBranch:doElem else $elseBranch:doElem)
