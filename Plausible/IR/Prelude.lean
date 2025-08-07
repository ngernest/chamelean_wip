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

/-- Computes the set of all free variables in an expression, returning a `HashSet` of `FVarId`s
    - This is a non-monadic version of `Lean.CollectFVars`, defined in
    https://github.com/leanprover/lean4/blob/6741444a63eec253a7eae7a83f1beb3de015023d/src/Lean/Util/CollectFVars.lean#L28 -/
def getFVarsSet (e : Expr) : HashSet FVarId :=
  open HashSet in
  match e with
  | .proj _ _ e => getFVarsSet e
  | .forallE _ ty body _ => union (getFVarsSet ty) (getFVarsSet body)
  | .lam _ ty body _ => union (getFVarsSet ty) (getFVarsSet body)
  | .letE _ ty val body _ =>
    union (getFVarsSet ty) (union (getFVarsSet val) (getFVarsSet body))
  | .app f a => union (getFVarsSet f) (getFVarsSet a)
  | .mdata _ e => getFVarsSet e
  | .fvar fvar_id => HashSet.ofArray #[fvar_id]
  | _ => ∅

/-- Extracts all the *unique* `FVarId`s in an expression, returning an array of `FVarID`s -/
def extractFVarIds (e : Expr) : Array FVarId :=
  HashSet.toArray $ getFVarsSet e

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

/-- Creates a fresh user-facing name with the prefix `username` and type `ty` in the `LocalContext` `lctx`,
    returning the updated context, associated `FVarId` and fresh name in the `MetaM` monad -/
def addFreshLocalDecl (lctx : LocalContext) (username : Name) (ty : Expr) : MetaM (LocalContext × FVarId × Name) :=
  withLCtx' lctx do
    let newname := getUnusedName lctx username
    withLocalDeclD newname ty $ fun expr =>
      return (← getLCtx, expr.fvarId!, newname)

/-- Creates a new `LocalDecl` with name `username` and type `ty`, returning the updated `LocalContext`
    and `FVarId` associated with the new `LocalDecl` -/
def addLocalDecl (lctx : LocalContext) (username : Name) (ty : Expr) : MetaM (LocalContext × FVarId) :=
  withLCtx' lctx do
    withLocalDeclD username ty $ fun expr =>
      return (← getLCtx, expr.fvarId!)

/-- `getFVarTypeInContext fvarId lctx` extracts the type associated with a `FVarId` in the context `lctx` -/
def getFVarTypeInContext (fvarId : FVarId) (lctx : LocalContext) : MetaM Expr :=
  match lctx.find? fvarId with
  | none => throwError "Cannot find FVarId associated with {fvarId.name} in LocalContext"
  | some localDecl => return localDecl.type

/-- Decomposes a universally-quantified type expression whose body is an arrow type
    (i.e. `∀ (x1 : τ1) … (xn : τn), Q1 → … → Qn → P`), and returns a triple of the form
    `(#[(x1, τ1), …, (xn, τn)], Q1 → … → Qn → P, #[Q1, …, Qn, P])`.
    - The 2nd component is the body of the forall-expression
    - The 3rd component is an array containing each subterm of the arrow type -/
def decomposeType (e : Expr) : MetaM (Array (Name × Expr) × Expr × Array Expr) := do
  let (binder, tyExpr) := extractForAllBinders e
  let arrowTypeComponents ← getComponentsOfArrowType tyExpr
  return (binder, tyExpr, arrowTypeComponents)


/-- Decomposes a universally-quantified type expression whose body is an arrow type
    (i.e. `∀ (x1 : τ1) … (xn : τn), Q1 → … → Qn → P`) using the `LocalContext` `lctx`,
    and returns a quadruple of the form
    `(#[(x1, τ1), …, (xn, τn)], Q1 → … → Qn → P, #[Q1, …, Qn, P], updated LocalContext)`.
    - The 2nd component is the body of the forall-expression
    - The 3rd component is an array containing each subterm of the arrow type -/
def decomposeTypeWithLocalContext (e : Expr) (lctx : LocalContext) : MetaM (Array (Name × Expr) × Expr × Array Expr × LocalContext) :=
  withLCtx' lctx do
    let (binder, exp) := extractForAllBinders e
    let mut new_exp := exp
    let mut lctx := lctx
    let mut new_binder := #[]
    for (name, ty) in binder do
      let (new_lctx, new_fvarid, newname) ← addFreshLocalDecl lctx name ty
      lctx := new_lctx
      let old_fvarid := ⟨name⟩
      let new_fvar := mkFVar new_fvarid
      new_exp := new_exp.replaceFVarId old_fvarid new_fvar
      new_binder := new_binder.push (newname, ty)
    let tyexp ← getComponentsOfArrowType new_exp
    return (new_binder, new_exp, tyexp, lctx)

/-- `mkEqualities pairs f lctx` creates an array of `Expr`s, where each `Expr` is an equality between each `α × α` pair in `pairs`.
    (Any pairs where the two components are definitionally equal are filtered out, since
    we want to avoid create trivial equalities.)

    The function `f` is used to convert `α` into `Expr`s using the `MetaM` monad, and the `LocalContext` `lctx` is updated
    after the equalities have been created.

    See `mkExprEqualities` & `mkFVarEqualities` for specialized versions of this function. -/
def mkEqualities (pairs : Array (α × α)) (f : α → MetaM Expr) (lctx : LocalContext) : MetaM (Array Expr) :=
  withLCtx' lctx do
    let mut equalities := #[]
    for (lhs, rhs) in pairs do
      let lhsExpr ← f lhs
      let rhsExpr ← f rhs
      -- Avoid creating an equality if LHS & RHS are definitionally equal
      if (← isDefEq lhsExpr rhsExpr) then
        continue
      else
        let eq ← mkEq lhsExpr rhsExpr
        equalities := equalities.push eq
    return equalities

/-- Version of `mkEqualities` where `α` is specialized to `Expr` -/
def mkExprEqualities (exprPairs : Array (Expr × Expr)) (lctx : LocalContext) : MetaM (Array Expr) :=
  mkEqualities exprPairs pure lctx

/-- Version of `mkEqualities` where `α` is specialized to `FVarId` -/
def mkFVarEqualities (fvarPairs : Array (FVarId × FVarId)) (lctx : LocalContext) : MetaM (Array Expr) :=
  mkEqualities fvarPairs (fun fvarId => LocalDecl.toExpr <$> FVarId.getDecl fvarId) lctx

/-- Decomposes an array `arr` into a pair `(xs, x)`
   where `xs = arr[0..=n-2]` and `x = arr[n - 1]` (where `n` is the length of `arr`).
   - If `arr` is empty, this function returns `none`
   - If `arr = #[x]`, this function returns `some (#[], x)`
   - Note: this function is the same as `unsnoc` in the Haskell's `Data.List` library -/
def splitLast? (arr : Array α) : Option (Array α × α) :=
  match arr.back? with
  | none => none
  | some a => some (arr.extract 0 (arr.size - 1), a)

/-- Converts an array of syntactic terms to an array of strings -/
def convertIdentsToStrings (terms : Array (TSyntax `term)) : Array String :=
  Array.map (fun term =>
    match term with
    | `($id:ident) => id.getId.toString
    | _ => toString term) terms

end Plausible.IR
