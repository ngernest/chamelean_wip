import Lean
import Std
import Plausible.IR.Examples
import Plausible.IR.Extractor
import Plausible.IR.Prelude
import Lean.Elab.Deriving.DecEq
import Lean.Meta.Tactic.Simp.Main

open Lean.Elab.Deriving.DecEq
open List Nat Array String
open Lean Elab Command Meta Term LocalContext
open Lean.Parser.Term
open Std

namespace Plausible.IR

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
  /-- The resultant hypothesis after all the fvars in `fvarIds` have been rewritten
      such that each fvar is unique -/
  newHypothesis : Expr

  /-- A collection of the `FVarId`s that appear in `newHypothesis`
     (including the new fvars that were produced) -/
  fVarIds : Array FVarId

  /-- A collection of equations relating pairs of `FVarId`s to each other
      (e.g. `t = t1`) -/
  variableEqualities : Array (FVarId × FVarId)

  LCtx: LocalContext

  variableEqs : Array Expr

  deriving Repr

/- keep the first occurence of the old FVarId in the expr, substitute the rest coccurences of it by the  new one-/
def keep_first_subst_rest_fvarids (hyp: Expr) (old: FVarId) (new: FVarId) (lctx: LocalContext): MetaM Expr := withLCtx' lctx do
  --The following tempfvarid is temporary for swapping and will not stay in the lctx, so we accept ←  mkFreshFVarId here
  let tempfvarid ←  mkFreshFVarId
  let mut newHyp := hyp
  newHyp ← subst_first_fVar newHyp old tempfvarid
  newHyp := newHyp.replaceFVarId old (mkFVar new)
  newHyp := newHyp.replaceFVarId tempfvarid (mkFVar old)
  return newHyp


/-
def separateFVars2 (hyp : Expr) (lctx: LocalContext): MetaM DecomposedInductiveHypothesis := withLCtx' lctx do
  let mut lctx := lctx
  let fvars := extractFVarIds hyp
  let mut equations : Array (FVarId × FVarId) := #[]
  let mut fVarIds := fvars
  let mut newHyp := hyp
  for fv in fvars do
    let mut i := 0
    let mut currentFV := fv
    let ty ←  getFVarId_type fv lctx
    while (numMatchingFVars newHyp currentFV > 1) do
      let newName := Name.appendAfter fv.name s!"_{i}"
      withLocalDeclD newName ty fun _ => do
        newHyp ← keep_first_subst_rest_fvarids newHyp currentFV newFVarId (← getLCtx)
        i:= i + 1
        currentFV := newFVarId
        equations := equations.push (fv, newFVarId)
        fVarIds := fVarIds.push newFVarId
  let variableEqs ←  mkEqs_FvarIds equations lctx
  return {
    newHypothesis := newHyp
    fVarIds := fVarIds
    variableEqualities := equations
    LCtx := lctx
    variableEqs := variableEqs
  }
-/


/-- For each free variable `t` that appears more than once in the hypothesis `hyp`,
    replace its second occurrence with `t1`, its 3rd occurrence with `t2`, etc.,
    and record the equalities `t = t1, t = t2, ...` -/
def separateFVars (hyp : Expr) (lctx: LocalContext): MetaM DecomposedInductiveHypothesis := withLCtx' lctx do
  let mut lctx := lctx
  let fvars := extractFVarIds hyp
  let mut equations : Array (FVarId × FVarId) := #[]
  let mut fVarIds := fvars
  let mut newHyp := hyp
  for fv in fvars do
    let mut i := 0
    let mut currentFV := fv
    while (numMatchingFVars newHyp currentFV > 1) do
      let ty ←  getFVarId_type fv lctx
      let newName := Name.appendAfter fv.name s!"_{i}"
      let (new_lctx, newFVarId) ←  mkNewFVarId lctx newName ty
      lctx := new_lctx
      newHyp ← keep_first_subst_rest_fvarids newHyp currentFV newFVarId lctx
      i:= i + 1
      currentFV := newFVarId
      equations := equations.push (fv, newFVarId)
      fVarIds := fVarIds.push newFVarId
  let variableEqs ←  mkEqs_FvarIds equations lctx
  return {
    newHypothesis := newHyp
    fVarIds := fVarIds
    variableEqualities := equations
    LCtx := lctx
    variableEqs := variableEqs
  }

/-- Variant of `separateFVars` that only examines
    the free variables in `hypothesis` that appear in `initialFVars`,
    and uses the index of the hypothesis (`hypIndex`) to generate fresh names -/
def separateFVarsInHypothesis (hypothesis : Expr) (initialFVars : Array FVarId) (hypIndex : Nat) (lctx: LocalContext)
    : MetaM DecomposedInductiveHypothesis := do withLCtx' lctx do
  let mut lctx := lctx
  let initializedFVars := Array.intersect (extractFVarIds hypothesis) initialFVars
  let mut newHypothesis := hypothesis
  let mut equalities : Array (FVarId × FVarId) := #[]
  for fvar in initializedFVars do
    let fvarname ←  fvar.getUserName
    let newName := Name.mkStr1 (fvarname.toString ++ "_" ++ toString hypIndex)
    let ty ←  getFVarId_type fvar lctx
    let (new_lctx, newFVarId) ← mkNewFVarId lctx newName ty
    lctx := new_lctx
    newHypothesis := newHypothesis.replaceFVarId fvar (mkFVar newFVarId)
    equalities := equalities.push (fvar, newFVarId)
  let decomposedHypothesis ← separateFVars newHypothesis lctx
  let variableEqualities := equalities ++ decomposedHypothesis.variableEqualities
  let variableEqs ←  mkEqs_FvarIds variableEqualities lctx
  return {
    newHypothesis := decomposedHypothesis.newHypothesis
    fVarIds := initializedFVars ++ decomposedHypothesis.fVarIds
    variableEqualities := variableEqualities
    variableEqs := variableEqs
    LCtx := decomposedHypothesis.LCtx
  }

/-- The `GenerationStyle` datatype describes the "style" in which a generator should be invoked:
    - `RecursiveCall` indicates that we should recursively call the current generator function
    - `TypeClassResolution` indicates that we should call the generator via typeclass resolution
      (i.e. call the generator from the `Arbitrary` / `ArbitrarySizedSuchThat` typeclass) -/
inductive GenerationStyle
  | RecursiveCall
  | TypeClassResolution
  deriving Repr

/-- Represents an expression in the RHS of the non-trivial pattern-match case
    in a backtrack element (sub-generator)
  - Note: this datatype was formerly known as `GenCheckCall`
  - TODO (Ernest): this is a super-set of QuickChick's `schedule_step`
      (maybe just take `ret` out and have it be a separate thing, since we can only
       have `return`s at the end of a schedule
       - also Checkers don't have `return`s) -/
inductive Action where
  /-- Invoke a checker for the inductive relation specified in the hypothesis `hyp`
      (`hyp` must be an inductive relation) -/
  | checkInductive (hyp : Expr)

  /-- The hypothesis `hyp` is not an inductive relation, but a function that returns
      `Prop`, so we invoke a checker that determines whether the `Prop` is true -/
  | checkNonInductive (hyp : Expr)

  /-- Generate an input at the given position `pos` for an inductive relation
      specified by `hyp`. The generated value is assigned to the free variable `fvar`.
      The generator is to be called using the `style` specified by the `GenerationStyle` type -/
  | genInputForInductive (fvar : FVarId) (hyp : Expr) (pos : Nat) (style : GenerationStyle)

  /-- Match the `fvar` with the shape of the hypothesis `hyp` using an `if let` expression
      - `matchFVar` always comes after a `genFVar`
      - Produces code of the form `if let hyp := fvar then ...` -/
  | matchFVar (fvar : FVarId) (hyp : DecomposedInductiveHypothesis)

  /-- Generate a free variable `fvar` with the given `type`
      - This is `gen_UC` (unconditional generation) in the QuickChick codebase (i.e. `arbitrary`) -/
  | genFVar (fvar : FVarId) (type : Expr)

  /-- `return` the expression `e` in some ambient monad (e.g. `Gen`) -/
  | ret (e : Expr)

  deriving Repr

structure ConstructorActions where
  actions : Array Action
  Lctx: LocalContext

/-- Extracts all the free variables in the conclusion of a constructor
    for an inductive relation -/
def getFVarsInConclusion (ctor : InductiveConstructor) : Array FVarId :=
  extractFVarIds ctor.conclusion

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
      outarr := Array.appendUniqueElements outarr (extractFVarIds argExpr)
    i := i + 1
  return outarr

def get_producer_outset (c: InductiveConstructor) (genpos: Nat): MetaM (Array FVarId) := do
  if h: genpos ≥ c.conclusion_args.size then throwError "invalid gen position"
  else
    let initset ← getFVarsInConclusionArgs c genpos
    let gen_arg := c.conclusion_args[genpos]
    let outvar := extractFVarIds gen_arg
    let mut outarr : Array FVarId := #[]
    for i in initset do
      if ¬ Array.elem i outvar then outarr:=outarr.push i
    return outarr

/-- Removes all free variables in an expression `e` from `fvars`, returning
    the resultant collection of `FVarId`s -/
def getUninitializedFVars (e : Expr) (fvars : Array FVarId) : Array FVarId :=
  Array.removeAll (extractFVarIds e) fvars

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
    3. The collection of free variables in the argument that have yet to be initialized -/
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
      fVarsToBeInitialized := extractFVarIds arg
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


def Actions_for_hypotheses (ctor : InductiveConstructor) (fvars : Array FVarId) : MetaM ConstructorActions := do
  let mut lctx := ctor.LCtx
  let mut actions := #[]
  let mut initializedFVars := fvars
  for (hyp, i) in ctor.all_hypotheses.zipIdx do
    let isHypOfInductiveCtor ← isHypothesisOfInductiveConstructor hyp ctor

    if isHypOfInductiveCtor then
      if allFVarsInExprInitialized hyp initializedFVars then
        actions := actions.push (.checkInductive hyp)
      else
        let (uninitializedArgIdx, uninitializedFVars, fVarsToBeInitialized)
          ← getLastUninitializedArgAndFVars hyp initializedFVars

        for fid in uninitializedFVars do
          let ty ← getFVarId_type fid lctx
          actions := actions.push (.genFVar fid ty)

        let argToGenerate := hyp.getAppArgs[uninitializedArgIdx]!


        initializedFVars := Array.appendUniqueElements initializedFVars uninitializedFVars

        let generationStyle :=
          if hypothesisRecursivelyCallsCurrentInductive hyp ctor
          then .RecursiveCall
          else .TypeClassResolution


        if argToGenerate.isFVar then
          let fvarToGenerate := argToGenerate.fvarId!
          actions := actions.push (.genInputForInductive fvarToGenerate hyp uninitializedArgIdx generationStyle)
        else
          let nameOfFVarToGenerate := Name.mkStr1 ("tcond" ++ toString i)
          let ty ← inferType argToGenerate
          let (new_lctx, fvarToGenerate) ←  mkNewFVarId lctx nameOfFVarToGenerate ty
          lctx:= new_lctx
          let decomposedHypothesis ← separateFVarsInHypothesis argToGenerate initializedFVars i lctx
          lctx := decomposedHypothesis.LCtx
          actions := actions.push (.genInputForInductive fvarToGenerate hyp uninitializedArgIdx generationStyle)
          actions := actions.push (.matchFVar fvarToGenerate decomposedHypothesis)
        initializedFVars := Array.appendUniqueElements initializedFVars fVarsToBeInitialized
    else
      if allFVarsInExprInitialized hyp initializedFVars then
        actions := actions.push (.checkNonInductive hyp)
      else
        let uninitializedFVars := getUninitializedFVars hyp initializedFVars
        for fvar in uninitializedFVars do
          let ty ← getFVarId_type fvar lctx
          actions := actions.push (.genFVar fvar ty)
        initializedFVars := Array.appendUniqueElements initializedFVars uninitializedFVars
        actions := actions.push (.checkNonInductive hyp)

  return {
    actions := actions
    Lctx := lctx
  }




/-- Produces a collection of `Actions` for a checker -/
def Actions_for_checker (ctor : InductiveConstructor) : MetaM ConstructorActions := do
  let mut initset := getFVarsInConclusion ctor
  Actions_for_hypotheses ctor initset


/-- Produces a collection of `Actions` for a generator -/
def Actions_for_producer (ctor : InductiveConstructor) (genpos : Nat) : MetaM ConstructorActions := do
  let mut initset ← getFVarsInConclusionArgs ctor genpos
  let mut init_actions ← Actions_for_hypotheses ctor initset
  let mut actions := init_actions.actions
  let lctx := init_actions.Lctx
  for hyp in ctor.all_hypotheses do
    initset := Array.appendUniqueElements initset (extractFVarIds hyp)
  let gen_arg := ctor.conclusion.getAppArgs[genpos]!
  let uninitset := Array.removeAll (extractFVarIds gen_arg) initset
  for fid in uninitset do
    let ty ← getFVarId_type fid lctx
    actions := actions.push (Action.genFVar fid ty)
  actions := actions.push (Action.ret gen_arg)
  return {
    actions := actions
    Lctx := lctx
  }




/-- Note: this function is purely for debugging purposes, it is not used in the main algorithm -/
def Actions_toStr (c: Action) : MetaM String := do
  match c with
  | .checkInductive cond => return "check_IR_" ++ toString (← Meta.ppExpr cond)
  | .checkNonInductive cond => return "check_nonIR_" ++ toString (← Meta.ppExpr cond)
  | .genInputForInductive _ cond pos _ =>  return  "gen_IR_" ++ toString (← Meta.ppExpr cond) ++ " at "  ++ toString pos
  | .matchFVar fvar hypothesis => return  "if let " ++ toString (← Meta.ppExpr hypothesis.newHypothesis) ++ ":= " ++ toString (fvar.name) ++ " then "
  | .genFVar id ty =>  return  "gen_FVar " ++ toString (id.name) ++ ": " ++ toString (← Meta.ppExpr ty)
  | .ret e =>  return "return " ++ toString (← Meta.ppExpr e)

def gen_IR_at_pos (id: FVarId) (cond: Expr) (pos: Nat) (lctx: LocalContext): MetaM String := withLCtx' lctx do
  let tt := Lean.mkFVar ⟨Name.mkStr1 "tt"⟩
  let new_args := cond.getAppArgs.set! pos tt
  let new_cond := Lean.mkAppN cond.getAppFn new_args
  let fun_proto := "fun tt => " ++ toString (← Meta.ppExpr new_cond)
  return "let " ++ toString (← id.getUserName)  ++ ":= gen_IR (" ++ fun_proto ++ ")"


/-- Converts a `Action` data structure to a string containing the
    corresponding Lean expression
    - Note: this function is purely for debugging purposes, it is not used in the main algorithm -/
def Actions_toString (Action : Action) (lctx: LocalContext): MetaM String := withLCtx' lctx do
  match Action with
  | .checkInductive hyp => MessageData.toString m!"check_IR ({← Meta.ppExpr hyp})"
  | .checkNonInductive hyp => return  "check (" ++ toString (← Meta.ppExpr hyp) ++ ")"
  | .genInputForInductive fvar hyp pos _ => gen_IR_at_pos fvar hyp pos lctx
  | .matchFVar fvar hypothesis => return  "if let " ++ toString (← Meta.ppExpr hypothesis.newHypothesis) ++ ":= " ++ toString (← fvar.getUserName) ++ " then "
  | .genFVar id ty =>  return  "let " ++ toString (← id.getUserName) ++ ":= gen_rand " ++ toString (← Meta.ppExpr ty)
  | .ret e => return "return " ++ toString (← Meta.ppExpr e)


-- To pretty-print a `Action` idiomatically, we can just make it an instance
-- of the `ToMessageData` typeclass, which allows us to use Lean's delaborator
-- to pretty-print `Expr`s
instance : ToMessageData Action where
  toMessageData (Action : Action) : MessageData :=
    match Action with
    | .checkInductive hyp => m!"check_IR {hyp}"
    | .checkNonInductive hyp => m!"check_nonIR ({hyp})"
    | .genInputForInductive fvar hyp idx generationStyle =>
      match generationStyle with
      | .RecursiveCall =>
        let remainingArgs := (hyp.getAppArgs.eraseIdx! idx).toList
        m!"let {fvar.name} ← aux_arb size' {remainingArgs}"
      | .TypeClassResolution =>
        m!"let {fvar.name} ← ArbitrarySuchThat.arbitraryST (fun {fvar.name} => {hyp})"
    | .matchFVar fvar hypothesis => m!"if let {hypothesis.newHypothesis} := {fvar.name} then ..."
    | .genFVar fvar ty => m!"let {fvar.name} ← SampleableExt.interpSample {ty}"
    | .ret e => m!"return {e}"


def checker_header (con: InductiveConstructor) : MetaM String := do withLCtx' con.LCtx do
  let hyp: String := toString (← Array.mapM Meta.ppExpr con.all_hypotheses)
  let conclusion := toString (← Meta.ppExpr con.conclusion)
  return hyp ++ " → " ++ conclusion

syntax (name := getCheckerCall) "#get_checker_actions" term : command

@[command_elab getCheckerCall]
def elabCheckerCall : CommandElab := fun stx => do
  match stx with
  | `(#get_checker_actions $t1:term) =>
    Command.liftTermElabM do
      let inpexp ← elabTerm t1 none
      let relation ← getInductiveInfo inpexp
      for con in relation.constructors do
        IO.println s!"\n---- Constructor : {← checker_header con}"
        --IO.println s!"---- Out prop : {con.conclusion}"
        let proc_conds ← Actions_for_checker con
        for pc in proc_conds.actions do
          IO.println (← Actions_toString pc proc_conds.Lctx)
  | _ => throwError "Invalid syntax"


-- #get_checker_actions typing
#get_checker_actions balanced
#get_checker_actions bst

def producer_header (con: InductiveConstructor) : MetaM String := do withLCtx' con.LCtx do
  let hyp: String := toString (← Array.mapM Meta.ppExpr con.all_hypotheses)
  let conclusion := toString (← Meta.ppExpr con.conclusion)
  let arg: String := toString (← Array.mapM Meta.ppExpr con.conclusion_args)
  return hyp ++ " → " ++ conclusion ++ "\n---Args: " ++ arg

syntax (name := geGenCall) "#get_producer_actions" term "for_arg" num : command

@[command_elab geGenCall]
def elabGenCall : CommandElab := fun stx => do
  match stx with
  | `(#get_producer_actions $t1:term for_arg $t2) =>
    Command.liftTermElabM do
      let inpexp ← elabTerm t1 none
      let pos := TSyntax.getNat t2
      let relation ← getInductiveInfo inpexp
      for ctor in relation.constructors do
        IO.println s!"\n---- Constructor : {← checker_header ctor}"
        let producer_Actions ← Actions_for_producer ctor pos
        for Action in producer_Actions.actions do
          IO.println (← Actions_toString Action producer_Actions.Lctx)
  | _ => throwError "Invalid syntax"


#get_producer_actions typing for_arg 2
-- #get_producer_actions balanced for_arg 1
#get_producer_actions bst for_arg 1

end Plausible.IR
