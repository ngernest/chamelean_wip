import Lean
import Std
import Plausible.IR.Example
import Plausible.IR.Extractor
import Plausible.IR.Prelude
import Lean.Elab.Deriving.DecEq
import Lean.Meta.Tactic.Simp.Main

open Lean.Elab.Deriving.DecEq
open List Nat Array String
open Lean Elab Command Meta Term
open Lean.Parser.Term
open Std

namespace Plausible.IR

-- Process condition ---

/-- Removes all elements of `xs` that are present in `ys`
    (variant of `List.removeAll` for arrays) -/
def Array.removeAll [BEq α] (xs : Array α) (ys : Array α) : Array α :=
  (List.removeAll xs.toList ys.toList).toArray

/-- Computes the intersection of two lists -/
def List.intersect [BEq α] (xs : List α) (ys: List α) : List α :=
  match xs with
  | [] => []
  | h::t => if List.elem h ys then h::List.intersect t ys else List.intersect t ys

/-- Computes the intersection of two arrays -/
def Array.intersect [BEq α] (xs : Array α) (ys : Array α) : Array α :=
  (List.intersect xs.toList ys.toList).toArray

/-- Takes `xs` and appends all elements in `ys` that aren't in `xs` to `xs` -/
def List.appendUniqueElements [BEq α] (xs : List α) (ys : List α) : List α :=
  match ys with
  | [] => xs
  | h::t => if !(List.elem h xs) then List.appendUniqueElements (List.concat xs h) t
            else List.appendUniqueElements xs t

/-- Takes `xs` and appends all elements in `ys` that aren't in `xs` to `xs` -/
def Array.appendUniqueElements [BEq α] (xs : Array α) (ys : Array α) : Array α :=
  (List.appendUniqueElements xs.toList ys.toList).toArray

/-- `numMatchingFVars e id` returns the no. of `FVarId`s in
     an expression `e` that are equal to `id` -/
def numMatchingFVars (e : Expr) (id : FVarId) : Nat :=
  match e with
  | Expr.fvar fid => if id == fid then 1 else 0
  | Expr.app f a =>
    let c1 := numMatchingFVars f id
    let c2 := numMatchingFVars a id
    c1 + c2
  | _ => 0

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
def extractFVars (e : Expr) : Array FVarId :=
  HashSet.toArray $ getFVarsSet e

/-- A monadic version of `extractFVars` (which collects the array of `FVarId`s
    in the `MetaM` monad ) -/
def extractFVarsMetaM (e : Expr) : MetaM (Array FVarId) := do
  let (_, fvars_state) ← e.collectFVars.run {}
  return fvars_state.fvarIds


def subst_first_fVar (e: Expr) (old : FVarId) (new : FVarId) : MetaM Expr := do
  if ¬ e.containsFVar old then return e
  else
    match e with
    | Expr.fvar id =>
      if id == old then return (Expr.fvar new) else return e
    | Expr.app f a =>
      if f.containsFVar old then
        let fnew ← subst_first_fVar f old new
        return Expr.app fnew a
      else
        let anew ← subst_first_fVar a old new
        return Expr.app f anew
    | _ => return e

/-- `DecomposedInductiveHypothesis` represents a hypothesis where the free variables
     in `fVarId`s have equalities on them as stipulated by the `variableEqualities` field,
     (which maps old `FVarId`s to new `FVarId`s), and `newHypothesis` is the resultant
     hypothesis after all the `FVarId`s have been rewritten according to `variableEqualities` -/
structure DecomposedInductiveHypothesis where
  newHypothesis : Expr
  fVarIds : Array FVarId
  variableEqualities : Array (FVarId × FVarId)

/-- For each free variable `t` that appears more than once in the hypothesis `hyp`,
    replace its second occurrence with `t1`, its 3rd occurrence with `t2`, etc.,
    and record the equalities `t = t1, t = t2, ...` -/
def separateFVars (hyp : Expr) : MetaM DecomposedInductiveHypothesis := do
  let fvars := extractFVars hyp
  let mut equations : Array (FVarId × FVarId) := #[]
  let mut fVarIds := fvars
  let temp := Name.mkStr1 "temp000"
  let tempfvarid := FVarId.mk temp
  let mut newHyp := hyp
  for fv in fvars do
    let mut i := 0
    let mut currentFV := fv
    while (numMatchingFVars newHyp currentFV > 1) do
      let newName := Name.mkNum fv.name i
      let newFVarId := FVarId.mk newName
      newHyp ← subst_first_fVar newHyp currentFV tempfvarid
      newHyp := newHyp.replaceFVarId currentFV (mkFVar newFVarId)
      newHyp := newHyp.replaceFVarId tempfvarid (mkFVar currentFV)
      i:= i + 1
      currentFV := newFVarId
      equations := equations.push (fv, newFVarId)
      fVarIds := fVarIds.push newFVarId
  return {
    newHypothesis := newHyp
    fVarIds := fVarIds
    variableEqualities := equations
  }

/-- Variant of `separateFVars` that only examines
    the free variables in `hypothesis` that appear in `initialFVars`,
    and uses the index of the hypothesis (`hypIndex`) to generate fresh names -/
def separateFVarsInHypothesis (hypothesis : Expr) (initialFVars : Array FVarId)
  (hypIndex : Nat) : MetaM DecomposedInductiveHypothesis := do
  let initializedFVars := Array.intersect (extractFVars hypothesis) initialFVars
  let mut newHypothesis := hypothesis
  let mut equalities : Array (FVarId × FVarId) := #[]
  for fvar in initializedFVars do
    let newName := Name.mkStr1 (fvar.name.toString ++ "_" ++ toString hypIndex)
    let newFVarId := FVarId.mk newName
    newHypothesis := newHypothesis.replaceFVarId fvar (mkFVar newFVarId)
    equalities := equalities.push (fvar, newFVarId)
  let decomposedHypothesis ← separateFVars newHypothesis
  return {
    newHypothesis := decomposedHypothesis.newHypothesis
    fVarIds := initializedFVars ++ decomposedHypothesis.fVarIds
    variableEqualities := equalities ++ decomposedHypothesis.variableEqualities
  }



--TO BE IMPLEMENT-- separate function call with constructor

def is_inductive_constructor (e: Expr) : Bool := ¬ e.isFVar


inductive GenCheckCall where
  /-- Invoke a checker for the inductive relation specified in the hypothesis `hyp` -/
  | check_IR (hyp : Expr) : GenCheckCall
  | check_nonIR (hyp : Expr) : GenCheckCall
  | gen_IR (fvar : FVarId) (hyp : Expr) (pos : Nat): GenCheckCall
  /-- Match the `fvar` with the shape of the hypothesis `hyp` using an `if let` expression -/
  | matchFVar (fvar : FVarId) (hyp : DecomposedInductiveHypothesis) : GenCheckCall
  /-- Generate a free variable `fvar` with the given `type` -/
  | genFVar (fvar : FVarId) (type : Expr) : GenCheckCall
  /-- `return` the expression `e` in the `Gen` monad -/
  | ret (e : Expr): GenCheckCall

/-- Extracts all the free variables in the conclusion of a constructor
    for an inductive relation -/
def getFVarsInConclusion (ctor : InductiveConstructor) : Array FVarId :=
  extractFVars ctor.conclusion

/-- Takes a constructor for an inductive relation,
    and collects the free variables in each of the arguments for the constructor's conclusion
    (except for the argument which we wish to generate, indicated by its index `genpos`) -/
def getFVarsInConclusionArgs (ctor : InductiveConstructor) (genpos : Nat) : MetaM (Array FVarId) := do
  if genpos ≥ ctor.conclusion_args.size
    then throwError "invalid gen position"
  let mut i := 0
  let mut outarr := #[]
  for argExpr in ctor.conclusion_args do
    if i != genpos then
      outarr := Array.appendUniqueElements outarr (extractFVars argExpr)
    i := i + 1
  return outarr

def get_producer_outset (c: InductiveConstructor) (genpos: Nat): MetaM (Array FVarId) := do
  if h: genpos ≥ c.conclusion_args.size then throwError "invalid gen position"
  else
    let initset ← getFVarsInConclusionArgs c genpos
    let gen_arg := c.conclusion_args[genpos]
    let outvar := extractFVars gen_arg
    let mut outarr : Array FVarId := #[]
    for i in initset do
      if ¬ Array.elem i outvar then outarr:=outarr.push i
    return outarr

/-- Removes all free variables in an expression `e` from `fvars`, returning
    the resultant collection of `FVarId`s -/
def getUninitializedFVars (e : Expr) (fvars : Array FVarId) : Array FVarId :=
  Array.removeAll (extractFVars e) fvars

/-- Determines if all the free variables in `fvars` have been
    initialized in the expression `e`  -/
def allFVarsInExprInitialized (e : Expr) (fvars : Array FVarId) : Bool :=
  (getUninitializedFVars e fvars).size == 0

/-- Retrieves the index of the last argument in the `hypothesis`
    that contains an uninitialized free variable from the collection `fvars`
    - Note: this function is currently unused -/
def getLastUninitializedArgIdx (hypothesis : Expr) (fvars : Array FVarId) : MetaM (Option Nat) := do
  if !(← isInductiveRelationApplication hypothesis) then
    throwError "not a inductive cond to get_last_uninit_arg "
  let args := hypothesis.getAppArgs
  let mut i := 0
  let mut pos := args.size + 1
  for arg in args do
    if !allFVarsInExprInitialized arg fvars then
      pos := i
    i := i + 1
  if pos == args.size + 1 then
    return none
  else
    return some pos

/-- Returns a triple consisting of:
    1. The index of the last argument in the `hypothesis` that contains an uninitialized free variable from the collection `fvars`
    2. A collection of all uninitialized free variables in the `hypothesis`
    3. The collection of free variables in the argument that have yet to be intiialize -/
def getLastUninitializedArgAndFVars
  (hypothesis : Expr) (fvars : Array FVarId) : MetaM (Nat × Array FVarId × Array FVarId) := do
  if !(← isInductiveRelationApplication hypothesis) then
    throwError "not a inductive cond to get_last_uninit_arg "
  let args := hypothesis.getAppArgs
  let mut i := 0
  let mut uninitializedArgIdx := args.size + 1
  let mut uninitializedArg := args[0]!
  let mut fVarsToBeInitialized := #[]
  for arg in args do
    if !allFVarsInExprInitialized arg fvars then {
      uninitializedArgIdx := i;
      uninitializedArg := arg;
      fVarsToBeInitialized := extractFVars arg
    }
    i := i + 1
  if uninitializedArgIdx == args.size + 1 then
    return (args.size + 1, #[], #[])
  let mut uninitializedFVars := #[]
  i := 0
  for arg in args do
    if i != uninitializedArgIdx then
      uninitializedFVars := Array.appendUniqueElements uninitializedFVars (getUninitializedFVars arg fvars)
  uninitializedFVars := Array.removeAll uninitializedFVars fVarsToBeInitialized
  return (uninitializedArgIdx, uninitializedFVars, fVarsToBeInitialized)


def GenCheckCalls_for_hypotheses (ctor : InductiveConstructor) (fvars : Array FVarId) : MetaM (Array GenCheckCall) := do
  let mut result := #[]
  let mut initializedFVars := fvars
  let mut i := 0
  for hyp in ctor.all_hypotheses do
    i := i + 1
    if (← isHypothesisOfInductiveConstructor hyp ctor) then
      if allFVarsInExprInitialized hyp initializedFVars then
        result := result.push (GenCheckCall.check_IR hyp)
      else
        let (uninitializedArgIdx, uninitializedFVars, fVarsToBeInitialized)
          ← getLastUninitializedArgAndFVars hyp initializedFVars
        for fid in uninitializedFVars do
          let ty := ctor.bound_var_ctx.get! fid
          result := result.push (.genFVar fid ty)
        let argToGenerate := hyp.getAppArgs[uninitializedArgIdx]!
        initializedFVars := Array.appendUniqueElements initializedFVars uninitializedFVars
        if argToGenerate.isFVar then
          let fvarToGenerate := argToGenerate.fvarId!
          result := result.push (GenCheckCall.gen_IR fvarToGenerate hyp uninitializedArgIdx)
        else
          let nameOfFVarToGenerate := Name.mkStr1 ("tcond" ++ toString i)
          let fvarToGenerate := FVarId.mk nameOfFVarToGenerate
          let decomposedHypothesis ← separateFVarsInHypothesis argToGenerate initializedFVars i
          result := result.push (GenCheckCall.gen_IR fvarToGenerate hyp uninitializedArgIdx)
          result := result.push (.matchFVar fvarToGenerate decomposedHypothesis)
        initializedFVars := Array.appendUniqueElements initializedFVars fVarsToBeInitialized
    else
      if allFVarsInExprInitialized hyp initializedFVars then
        result := result.push (GenCheckCall.check_nonIR hyp)
      else
        let uninitializedFVars := getUninitializedFVars hyp initializedFVars
        for fvar in uninitializedFVars do
          let ty := ctor.bound_var_ctx.get! fvar
          result := result.push (.genFVar fvar ty)
        initializedFVars := Array.appendUniqueElements initializedFVars uninitializedFVars
        result := result.push (GenCheckCall.check_nonIR hyp)
  return result

def GenCheckCalls_for_checker (ctor : InductiveConstructor) : MetaM (Array GenCheckCall) := do
  let mut initset := getFVarsInConclusion ctor
  GenCheckCalls_for_hypotheses ctor initset


def GenCheckCalls_for_producer (ctor : InductiveConstructor) (genpos : Nat) : MetaM (Array GenCheckCall) := do
  let mut initset ← getFVarsInConclusionArgs ctor genpos
  let mut outarr ← GenCheckCalls_for_hypotheses ctor initset
  for hyp in ctor.all_hypotheses do
    initset := Array.appendUniqueElements initset (extractFVars hyp)
  -- TODO: figure out how to extract the conclusion of the constructor so that we can produce
  -- the corresponding generator
  let gen_arg := ctor.conclusion.getAppArgs[genpos]!
  let uninitset := Array.removeAll (extractFVars gen_arg) initset
  for fid in uninitset do
    let ty := ctor.bound_var_ctx.get! fid
    outarr := outarr.push (GenCheckCall.genFVar fid ty)
  outarr := outarr.push (GenCheckCall.ret gen_arg)
  return outarr

-- TODO: figure out how each `GenCheckCall` is produced
def GenCheckCalls_toStr (c: GenCheckCall) : MetaM String := do
  match c with
  | GenCheckCall.check_IR cond => return  "check_IR_" ++ toString (← Meta.ppExpr cond)
  | GenCheckCall.check_nonIR cond => return  "check_nonIR_" ++ toString (← Meta.ppExpr cond)
  | GenCheckCall.gen_IR _ cond pos =>  return  "gen_IR_" ++ toString (← Meta.ppExpr cond) ++ " at "  ++ toString pos
  | GenCheckCall.matchFVar id sp => return "match " ++ id.name.toString ++ toString (← Meta.ppExpr sp.newHypothesis)
  | GenCheckCall.genFVar id ty=>  return  "gen_fvar " ++ toString (id.name) ++ ": " ++ toString (← Meta.ppExpr ty)
  | GenCheckCall.ret e =>  return  "ret " ++ toString (← Meta.ppExpr e)

def gen_IR_at_pos (id: FVarId) (cond: Expr) (pos: Nat) : MetaM String := do
  let tt := Lean.mkFVar ⟨Name.mkStr1 "tt"⟩
  let new_args := cond.getAppArgs.set! pos tt
  let new_cond := Lean.mkAppN cond.getAppFn new_args
  let fun_proto := "fun tt => " ++ toString (← Meta.ppExpr new_cond)
  return "let " ++ toString (id.name)  ++ ":= gen_IR (" ++ fun_proto ++ ")"

/-- Converts a `GenCheckCall` data structure to a string containing the
    corresponding Lean expression -/
def GenCheckCalls_toRawCode (genCheckCall : GenCheckCall) : MetaM String := do
  match genCheckCall with
  | .check_IR hyp => return  "check_IR (" ++ toString (← Meta.ppExpr hyp) ++ ")"
  | .check_nonIR hyp => return  "check (" ++ toString (← Meta.ppExpr hyp) ++ ")"
  | .gen_IR fvar hyp pos => gen_IR_at_pos fvar hyp pos
  | .matchFVar fvar hypothesis => return  "if let " ++ toString (← Meta.ppExpr hypothesis.newHypothesis) ++ ":= " ++ toString (fvar.name) ++ " then "
  | .genFVar id ty =>  return  "let " ++ toString (id.name) ++ ":= gen_rand " ++ toString (← Meta.ppExpr ty)
  | .ret e => return "return " ++ toString (← Meta.ppExpr e)



syntax (name := getCheckerCall) "#get_checker_call" term : command

@[command_elab getCheckerCall]
def elabCheckerCall : CommandElab := fun stx => do
  match stx with
  | `(#get_checker_call $t1:term) =>
    Command.liftTermElabM do
      let inpexp ← elabTerm t1 none
      let relation ← getInductiveInfo inpexp
      for con in relation.constructors do
        IO.println s!"\n---- Cond prop : {con.all_hypotheses}"
        IO.println s!"---- Out prop : {con.conclusion}"
        let proc_conds ← GenCheckCalls_for_checker con
        for pc in proc_conds do
          IO.println (← GenCheckCalls_toRawCode pc)
  | _ => throwError "Invalid syntax"


#get_checker_call typing
#get_checker_call balanced
#get_checker_call bst

syntax (name := geGenCall) "#get_producer_call" term "for_arg" num : command

@[command_elab geGenCall]
def elabGenCall : CommandElab := fun stx => do
  match stx with
  | `(#get_producer_call $t1:term for_arg $t2) =>
    Command.liftTermElabM do
      let inpexp ← elabTerm t1 none
      let pos := TSyntax.getNat t2
      let relation ← getInductiveInfo inpexp
      for ctor in relation.constructors do
        IO.println s!"\n---- Hypotheses : {ctor.all_hypotheses}"
        IO.println s!"---- Conclusion : {ctor.conclusion}"
        IO.println s!"---- Conclusion Args : {ctor.conclusion_args}"
        let producer_genCheckCalls ← GenCheckCalls_for_producer ctor pos
        for genCheckCall in producer_genCheckCalls do
          IO.println (← GenCheckCalls_toRawCode genCheckCall)
  | _ => throwError "Invalid syntax"


#get_producer_call typing for_arg 2
#get_producer_call balanced for_arg 1
#get_producer_call bst for_arg 2

end Plausible.IR
