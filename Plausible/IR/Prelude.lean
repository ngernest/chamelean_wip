import Lean
open List Nat Array String
open Lean Expr Elab Command Meta Term LocalContext
open Except
open Std

namespace Plausible.IR

set_option linter.missingDocs false

/-- Takes a type expression `tyExpr` representing an arrow type, and returns an array of type-expressions
    where each element is a component of the arrow type.
    For example, `getComponentsOfArrowType (A -> B -> C)` produces `#[A, B, C]`. -/
partial def getComponentsOfArrowType (tyExpr : Expr) : MetaM (Array Expr) := do
  let rec helper (e : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
    match e with
    | Expr.forallE name domain body _ =>
      withLocalDeclD name domain fun fvar => do
        helper (body.instantiate1 fvar) (acc.push domain)
    | e => return acc.push e
  helper tyExpr #[]

/-- Takes a universally-quantified expression of the form `∀ (x1 : τ1) … (xn : τn), body`
    and returns the pair `(#[(x1, τ1), …, (xn, τn)], body)` -/
partial def extractForAllBinders (e : Expr) : Array (Name × Expr) × Expr :=
  let rec go (e : Expr) (acc : Array (Name × Expr)) :=
    match e with
    | Expr.forallE n t b _ =>
      if b.hasLooseBVar 0 then
        go (b.instantiate1 (mkFVar ⟨n⟩)) (acc.push (n, t))
      else
        (acc, e)
    | _ => (acc, e)
  go e #[]

/-- Decomposes a universally-quantified type expression whose body is an arrow type
    (i.e. `∀ (x1 : τ1) … (xn : τn), Q1 → … → Qn → P`), and returns a triple of the form
    `(#[(x1, τ1), …, (xn, τn)], Q1 → … → Qn → P, #[Q1, …, Qn, P])`.
    - The 2nd component is the body of the forall-expression
    - The 3rd component is an array containing each subterm of the arrow type -/
def decomposeType (e : Expr) : MetaM (Array (Name × Expr) × Expr × Array Expr) := do
  let (binder, tyExpr) := extractForAllBinders e
  let arrowTypeComponents ← getComponentsOfArrowType tyExpr
  return (binder, tyExpr, arrowTypeComponents)

/-- Decomposes an array `arr` into a pair `(xs, x)`
   where `xs = arr[0..=n-2]` and `x = arr[n - 1]` (where `n` is the length of `arr`).
   - If `arr` is empty, this function returns `none`
   - If `arr = #[x]`, this function returns `some (#[], x)`
   - Note: this function is the same as `unsnoc` in the Haskell's `Data.List` library -/
def splitLast? (arr : Array α) : Option (Array α × α) :=
  match arr.back? with
  | none => none
  | some a => some (arr.extract 0 (arr.size - 1), a)

end Plausible.IR
