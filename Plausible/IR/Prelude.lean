import Lean
open List Nat Array String
open Lean Expr Elab Command Meta Term LocalContext
open Except
open Std

namespace Plausible.IR

set_option linter.missingDocs false

-- Enhanced debug function
def debugLocalContext : MetaM Unit := do
  let localCtx ← getLCtx
  logWarning m!"=== LOCAL CONTEXT DEBUG ==="
  logWarning m!"Local context size: {localCtx.size}"
  logWarning m!"Local context is empty: {localCtx.isEmpty}"

  if !localCtx.isEmpty then
    for localDecl in localCtx do
      if !localDecl.isImplementationDetail then
        logWarning m!"  {repr localDecl.fvarId}: {localDecl.userName} : {localDecl.type}"
  else
    logWarning m!"❌ Local context is completely empty!"

def type_of_Name (name : Name) : MetaM Expr := do
  -- Try to get constant info first (for definitions, theorems, etc)
  match (← getEnv).find? name with
  --| some (ConstantInfo.inductInfo info)
  | some (ConstantInfo.defnInfo info) =>
    IO.println s!"  Def Info : {info.value}"
    let val := info.value
    let type ← inferType val
    return type
  | some (ConstantInfo.inductInfo info) =>
    IO.println s!"  Induct Info : {info.type}"
    let val := info.type
    let type ← inferType val
    return type
  | some (info) => return info.type
  -- For variables, try to get from local context
  | none => do
    match (← getLCtx).findFromUserName? name with
    | some localDecl => return localDecl.type
    | none => throwError "Cannot find type for name: {name}"

def Expr_of_Name (name : Name) : MetaM Expr := do
  -- Try to get constant info first (for definitions, theorems, etc)
  match (← getEnv).find? name with
  --| some (ConstantInfo.inductInfo info)
  | some (ConstantInfo.defnInfo info) =>
    IO.println s!"  Def Info : {info.value}"
    let val := info.value
    return val
  | some (ConstantInfo.inductInfo info) =>
    IO.println s!"  Induct Info : {info.type}"
    let val := info.type
    return val
  | some (info) => return info.type
  -- For variables, try to get from local context
  | none => do
    match (← getLCtx).findFromUserName? name with
    | some localDecl => return localDecl.toExpr
    | none => throwError "Cannot find type for name: {name}"

def printExpr_of_Name (name : Name) : MetaM Format := do
  let e ← Expr_of_Name name
  let m ← Meta.ppExpr e
  return m

def option_to_IO {α : Type} (o : Option α) (errorMsg : String := "Option is none") : IO α :=
  match o with
  | some a => return a
  | none => throw (IO.userError errorMsg)

def option_to_MetaM (o: Option α) (errmsg: String := "Option is none"): MetaM α := do
  match o with
  | some v => return v
  | _ => throwError errmsg

/-- Takes a type expression `tyexpr` representing an arrow type, and returns an array of type-expressions
    where each element is a component of the arrow type.
    For example, `getComponentsOfArrowType (A -> B -> C)` produces `#[A, B, C]`. -/
partial def getComponentsOfArrowType (tyexpr : Expr) : MetaM (Array Expr) := do
  let rec helper (e : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
    match e with
    | Expr.forallE _ domain body _ =>
      helper (body.instantiate1 (mkFVar ⟨`x⟩)) (acc.push domain)
    | e => return acc.push e
  helper tyexpr #[]

def typeArrayToString (types : Array Expr) : MetaM String := do
  let typeStrs ← types.mapM (fun t => do pure s!"{← Meta.ppExpr t}")
  return s!"[{String.intercalate ", " typeStrs.toList}]"

elab "#get_type" t:term : command => do
  Command.liftTermElabM do
    let e ← Term.elabTerm t none
    let types ← getComponentsOfArrowType e
    let typeStr ← typeArrayToString types
    IO.println typeStr

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

/-- Extracts the free variables in an expression, returning an array of `FVarID`s -/
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

/-- A monadic version of `extractFVarIds` (which collects the array of `FVarId`s
    in the `MetaM` monad ) -/
def extractFVarsMetaM (e : Expr) : MetaM (Array FVarId) := do
  let (_, fvars_state) ← e.collectFVars.run {}
  return fvars_state.fvarIds

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
  let (binder, exp) := extractForAllBinders e
  let tyexp ← getComponentsOfArrowType exp
  return (binder, exp, tyexp)


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
    The function `f` is used to convert `α` into `Expr`s using the `MetaM` monad, and the `LocalContext` `lctx` is updated
    after the equalities have been created.

    See `mkExprEqualities` & `mkFVarEqualities` for specialized versions of this function. -/
def mkEqualities (pairs : Array (α × α)) (f : α → MetaM Expr) (lctx : LocalContext) : MetaM (Array Expr) :=
  withLCtx' lctx do
    let mut equalities := #[]
    for (lhs, rhs) in pairs do
      let eq ← mkEq (← f lhs) (← f rhs)
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

def printConstructorsWithArgs (typeName : Name) : MetaM Unit := do
  IO.println s!"  Typename : {typeName}"
  let env ← getEnv
  match env.find? typeName with
  | none => throwError "Type '{typeName}' not found"
  | some (ConstantInfo.inductInfo info) => do
    IO.println s!"Constructors of {typeName}:"
    for ctorName in info.ctors do
      let some ctor := env.find? ctorName
        | throwError "Constructor '{ctorName}' not found"
      let (_, _, list_prop) ← decomposeType ctor.type
      match splitLast? list_prop with
      | some (cond_prop, out_prop) =>
      IO.println s!"  {ctorName} : {ctor.type}"
      IO.println s!" Cond prop : {cond_prop}"
      IO.println s!" Out prop:  {out_prop}"
      | none => IO.println s!"  not match"
  | some _ =>
    throwError "'{typeName}' is not an inductive type"

elab "#show_constructors" n:ident : command => do
  let typeName := n.getId
  Command.liftTermElabM do
    printConstructorsWithArgs typeName


partial def getFinalType (type : Expr) : MetaM Expr := do
  let rec go (e : Expr) : MetaM Expr := do
    match e with
    | Expr.forallE _ _ body _ => go (body.instantiate1 (mkFVar ⟨`_⟩))
    | e => return e
  go (← whnf type)

/-- Basic command to show final type -/
elab "#final_type" t:term : command => do
  Command.liftTermElabM do
    let e ← elabTerm t none
    let type ← inferType e
    let finalType ← getFinalType type
    IO.println s!"Original type: {← Meta.ppExpr type}"
    IO.println s!"Final type: {← Meta.ppExpr finalType}"


partial def getFirstType (type : Expr) : Option Expr := do
    match type with
    | Expr.forallE _ domain _ _ => some domain
    | _ => none


def print_Array_Expr (a: Array (Name × Expr)) : MetaM Unit :=do
  for (n,e) in a do
    let l := Meta.ppExpr e
    IO.println s!" Variants: {n} : {← l}"


def print_List_Expr (a: MetaM (List (Name × Expr))) : MetaM Unit := do
  print_Array_Expr (← a).toArray


def getVariantTypes (typename : Name) : MetaM (List (Name × Expr)) := do
  let env ← getEnv
  match env.find? typename with
  | none => throwError "Type '{typename}' not found"
  | some (ConstantInfo.inductInfo indInfo) => do
    let ctors := indInfo.ctors
    let mut types : List (Name × Expr) := []
    for ctorname in ctors do
      let some ctor := env.find? ctorname
        | throwError "Constructor '{ctorname}' not found"
      let ctorType := ctor.type
      let ctorName := ctor.name
      types := types.append [(ctorName,ctorType)]
    return types
  | some _ =>
    throwError "'{typename}' is not an inductive type"

def mkListLevel (n:Nat) : MetaM (List Level) := do
  let mut l : List Level := []
  for _ in [0:n] do
    l:= l ++ [.zero]
  return l

def getVariant_GenericType (type : Expr): MetaM (List (Name × Expr)) := do
  let env ← getEnv
  let typename:= type.getAppFn.constName
  let args := type.getAppArgs
  match env.find? typename with
  | none => throwError "Type '{typename}' not found"
  | some (ConstantInfo.inductInfo indInfo) => do
    let ctors := indInfo.ctors
    let mut types : List (Name × Expr) := []
    for ctorname in ctors do
      let some ctor := env.find? ctorname
        | throwError "Constructor '{ctorname}' not found"
      let ctorName := ctor.name
      let ctorExp := Lean.mkConst ctorName (← mkListLevel args.size)
      let app_type := (Lean.mkAppN ctorExp args)
      let type ← inferType app_type
      types := types.append [(ctorName,type)]
    return types
  | some _ =>
    throwError "'{typename}' is not an inductive type"


partial def getVariant_info (t : Name × Expr) : MetaM (List (Name × Expr)) := do
  let env ← getEnv
  let typename := t.1
  let type := t.2
  match env.find? typename with
  | none => getVariant_GenericType type
  | some (ConstantInfo.inductInfo indInfo) => do
    let ctors := indInfo.ctors
    let mut info : List (Name × Expr) := []
    for ctorname in ctors do
      let some ctor := env.find? ctorname
        | throwError "Constructor '{ctorname}' not found"
      let ctorType := ctor.type
      let ctorName := ctor.name
      info := info.append [(ctorName, ctorType)]
    return info
  | some _ =>
    throwError "'{typename}' is not an inductive type"

def is_Prod (type: Expr) : MetaM Bool := do
  let f := type.getAppFn
  let p := Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero]
  if ← isDefEq f p then return true
  return false

def is_ProdM (type: MetaM Expr) : MetaM Bool := do
  let f := (← type).getAppFn
  let p := Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero]
  if ← isDefEq f p then return true
  return false

/-- Converts a Lean list of terms into a list of strings -/
def termToStringList (stx : TSyntax `term) : TermElabM (List String) := do
  match stx with
  | `([$xs,*]) =>
    let arr_s := xs.getElems
    let mut result := []
    for x in arr_s do
      match x with
      | `($x:str) => result := result.append [x.getString]
      | _ => throwError s!"Expected string literal, got {x}"
    return result
  | _ => throwError "Expected list of terms"


def makeUnderscores (n : Nat) : String :=
  if n == 0 then
    ""
  else
    String.join (List.replicate n "_ ")

def makeUnderscores_commas (n : Nat) : String :=
  if n == 0 then
    ""
  else
    let out := String.join (List.replicate n "_ , ")
    ⟨out.data.dropLast.dropLast⟩

def makeIndents (n : Nat) : String :=
  if n == 0 then
    ""
  else
    String.join (List.replicate n " ")

def makeInputs_ptr (s: String) (n : Nat) := makeInputs_aux s n n
where makeInputs_aux (s: String) (n : Nat) (z: Nat) : String := match n with
| 0 => ""
| succ n => s ++ "_" ++ (toString (z - n) ) ++ " " ++ (makeInputs_aux s n z)

def afterLastDot (s : String) : String :=
  match s.revFind (· == '.') with
  | none => s  -- no dot found, return the whole string
  | some i => s.drop (i.byteIdx + 1)  -- found dot at index i, return substring after it


def makeInputs (s: String) (n : Nat) := makeInputs_aux s n n
where makeInputs_aux (s: String) (n : Nat) (z: Nat) : List String := match n with
| 0 => []
| succ n => [s  ++ (toString (z - n) )] ++ (makeInputs_aux s n z)


def print_m_string (m: MetaM String) : MetaM Unit := do
  IO.println s!"{← m}"

def print_m_arr_string (a: MetaM (Array String)) : MetaM Unit :=do
  for m in ← a do
    IO.println s!"{m}"

def parseCommand (input : String) : CommandElabM Unit := do
  let env ← getEnv
  match Parser.runParserCategory env `command input with
  | Except.ok stx =>
    IO.println s!"Parsed successfully: {stx}"
    elabCommand stx
    --runFrontend (processCommand stx) {} {} -- Executes the parsed command
  | Except.error err => IO.println s!"Parse error: {err}"

def parseCommands (inputs : Array String) : CommandElabM Unit := do
  let env ← getEnv
  for input in inputs do
    match Parser.runParserCategory env `command input with
    | Except.ok stx =>
      IO.println s!"Parsed successfully: {stx}"
      elabCommand stx
      --runFrontend (processCommand stx) {} {} -- Executes the parsed command
    | Except.error err => IO.println s!"Parse error: {err}"

/-- Converts an array of syntactic terms to an array of exprs that are all
    `Expr`s created using the `Expr.fvar` constructor -/
def convertIdentsToFVarExprs (terms : Array (TSyntax `term)) : Array Expr :=
  Array.map (fun term =>
    let name :=
      match term with
      | `($id:ident) => id.getId.toString
      | _ => toString term
    Expr.fvar (FVarId.mk (Name.mkStr1 name))) terms

/-- Converts an array of syntactic terms to an array of strings -/
def convertIdentsToStrings (terms : Array (TSyntax `term)) : Array String :=
  Array.map (fun term =>
      match term with
      | `($id:ident) => id.getId.toString
      | _ => toString term) terms

end Plausible.IR
