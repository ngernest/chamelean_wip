/-
Copyright (c) 2025 Ernest Ng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ernest Ng
-/
import Lean.Expr
import Lean.Meta
open Lean Meta Parser


/-!
# Combinators for `TSyntax`

This file contains combinators for creating `TSyntax` terms and monadic expressions (`doElem`s),
which are used when deriving the code for generators.


## References
* https://leanprover-community.github.io/lean4-metaprogramming-book/main/05_syntax.html

-/

/-- Constructs a Lean monadic `do` block out of an array of `doSeq`s
    (expressions that appear in the `do` block) -/
def mkDoBlock (doElems : TSyntaxArray `doElem) : MetaM (TSyntax `term) := do
  `(do $[$doElems:doElem]*)

/-- `mkIfExprWithNaryAnd predicates trueBranch elseBranch` creates a *monadic* if-expression
    `if (p1 && … && pn) then $trueBranch else $elseBranch`, where `predicates := #[p1, …, pn]`.
    Note:
    - `trueBranch` and `elseBranch` are `doElem`s, since the if-expr is intended to be part of
    a monadic `do`-block
    - If `predicates` is empty, the expression created is `if True then $trueBranch else $elseBranch` -/
def mkIfExprWithNaryAnd (predicates : Array Term)
  (trueBranch : TSyntax `doElem) (elseBranch : TSyntax `doElem) : MetaM (TSyntax `doElem) := do
  let condition ←
    match predicates.toList with
    | [] => `(True)
    | [p] => pure p
    | p :: ps =>
      List.foldlM (fun acc pred => `($acc && $pred)) (init := p) ps
  `(doElem| if $condition then $trueBranch:doElem else $elseBranch:doElem)
