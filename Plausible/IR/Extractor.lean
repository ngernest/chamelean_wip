import Lean
import Std
import Plausible.IR.Example
import Plausible.IR.Prelude
import Lean.Elab.Deriving.DecEq
open Lean.Elab.Deriving.DecEq
open List Nat Array String
open Lean Elab Command Meta Term
open Lean.Parser.Term

-- We bring in the `Std` namespace so that we can refer to `HashMap` functions easily
open Std


namespace Plausible.IR

/- CODE -/

/-- Determines whether a type expression is an inductive relation -/
def isInductiveRelation (tyexpr : Expr) : MetaM Bool := do
  if ! (← Meta.isInductivePredicate tyexpr.constName) then
    return false
  let ty ← inferType tyexpr
  let arrow_type_components ← getComponentsOfArrowType ty
  -- Return type must be `Prop` in order for `tyexpr` to be an inductive relation
  let return_type := arrow_type_components.toList.getLast!
  return return_type.isProp

/-- Determines whether a type expression corresponds to the name of a base type (`Nat, String, Bool`) -/
def isBaseType (tyexpr : Expr) : Bool :=
  tyexpr.constName ∈ [`Nat, `String, `Bool]

/-- Extracts the types of all the arguments to an expression -/
partial def all_args_types (e : Expr) : MetaM (Array Expr) := do
  let args := e.getAppArgs
  if e.isFVar then
    return #[]
  if args.size == 0 then
    try
      let ty ← inferType e
      if isBaseType e then
        return #[e]
      else
        return ty.getAppArgs
    catch _ => return #[e]
  let mut out : Array Expr := #[]
  for arg in args do
    let arg_types ← all_args_types arg
    out := out.append arg_types
  return out

/-- Determines whether all the arguments to an expression have base types as their type
     -/
def allArgsHaveBaseTypes (e : Expr) : MetaM Bool := do
  let types ← all_args_types e
  pure $ (types.size > 0) ∧ (∀ t ∈ types, isBaseType t)


def mkFVars (a : Array Name) : Array Expr := a.map (fun x => mkFVar ⟨x⟩)

/-- `ConstructorType` describes a universally-quantified type expression whose body is an arrow type,
     i.e. types of the form `∀ (x1 : τ1) … (xn : τn), Q1 → … → Qn → P`.
    - `ConstructorType` is a triple containing three components:
    `(#[(x1, τ1), …, (xn, τn)], Q1 → … → Qn → P, #[Q1, …, Qn, P])`.
    - Note: The 2nd component is the body of the forall-expression
    - Note: The 3rd component is an array containing each subterm of the arrow type -/
abbrev DecomposedConstructorType := Array (Name × Expr) × Expr × Array Expr

structure IRConstructor where
  -- Bound variables and their types
  bound_vars: Array Name
  bound_var_ctx : HashMap FVarId Expr
  bound_vars_with_base_types : Array Name
  bound_vars_with_non_base_types : Array Name

  -- Metadata about each of the constructor's hypotheses
  all_hypotheses : Array Expr
  recursive_hypotheses: Array Expr
  hypotheses_with_only_base_type_args : Array Expr
  hypotheses_that_are_inductive_applications: Array Expr
  nonlinear_hypotheses: Array Expr

  -- Metadata about the constructor's conclusion
  conclusion : Expr
  final_arg_in_conclusion : Expr
  conclusion_args : Array Expr

  inp_eq: Array (Expr × Expr)
  ctor_expr: Expr
  num_inp_eq: Array (Expr × Expr)
  notnum_inp_eq: Array (Expr × Expr)
  name_space: Name
  dependencies: Array Expr

structure IR_info where
  name : Name
  input_type_names : Array Name
  output_type_name : Name
  input_types : Array Expr
  output_type : Expr
  input_vars: Array Expr
  output_vars : Expr
  input_var_names: Array (Option Name)
  output_var_names : Option Name
  decomposed_ctor_types : Array DecomposedConstructorType
  constructors : Array IRConstructor
  nocond_constructors : Array IRConstructor
  cond_constructors : Array IRConstructor
  dependencies: Array Expr

/-- Determines if an expression `e` is an application of the form `R e1 ... en`,
    where `R` is an inductive relation  -/
def isInductiveRelationApplication (e : Expr) : MetaM Bool := do
  match e.getAppFn.constName? with
  | some typeName => Meta.isInductivePredicate typeName
  | none => return false

/-- Determines whether an expression `e` is a hypothesis of a constructor `ctor`
   for an inductive relation -/
def isHypothesisOfInductiveConstructor (e : Expr) (ctor : IRConstructor) : MetaM Bool := do
  if !(← isInductiveRelation e.getAppFn) then
    return false
  if e.getAppFn.constName.getRoot == ctor.name_space then
    return true
  return false

/-- Determines whether an expression `e` is a dependency of an inductive relation
    (i.e. if `e` is an inductive relation that is defined within the current namespace) -/
def isDependency (e : Expr) (current_namespace : Name) : MetaM Bool := do
  if !(← isInductiveRelation e) then
    return false
  if e.constName.getRoot == current_namespace then
    return true
  return false

/-- Takes each argument in `input_args` and produces a corresponding `FVarId`,
    replacing the `i`-th argument in `conclusion` (if it is an application)
    with the `FVarId` corresponding to the `i`-th `input_arg` -/
def extract_fvars (conclusion : Expr) (input_args : List String) : MetaM (List (FVarId × Expr)) := do
  let fvar_ids := input_args.map (FVarId.mk ∘ Name.mkStr1)
  let new_input_args := fvar_ids.map Expr.fvar
  let conclusion_args_and_new_inputs := List.zip (conclusion.getAppArgs.toList) new_input_args
  pure $ List.filterMap (fun (conclusion_arg, new_expr) =>
    if conclusion_arg.isFVar then some (conclusion_arg.fvarId!, new_expr)
    else none) conclusion_args_and_new_inputs

/-- Replaces all occurrences of `FVarId`s in `e` using the association list `fvar_ids`, which
    maps each `FVarId` to an `expr` -/
def replace_fvars_in_expr (e : Expr) (fvar_ids : List (FVarId × Expr)) : MetaM Expr := do
  let mut newcond := e
  for (fvar_id, expr) in fvar_ids do
    newcond := newcond.replaceFVarId fvar_id expr
  return newcond

/-- For each `e` in `exprs_arr`, this function replaces all occurrences of `FVarId`s in `e`
    using the association list `fvar_ids`, which maps each `FVarId` to an `expr` -/
def replace_fvars_in_exprs (exprs_arr : Array Expr) (fvar_ids: List (FVarId × Expr)) : MetaM (Array Expr) :=
  Array.mapM (fun x => replace_fvars_in_expr x fvar_ids) exprs_arr

/-- Unifies each argument in `arg_names` with each variable in the `conclusion`, returning
    the updated `hypotheses`, `conclusion` and `bound_var_ctx`. If `arg_names` is empty,
    this function just returns `hypotheses`, `conclusion` & `bound_var_ctx` as is. -/
def unify_args_with_conclusion (hypotheses : Array Expr) (conclusion : Expr) (arg_names : List String)
  (bound_var_ctx : HashMap FVarId Expr) := do
  if List.isEmpty arg_names then
    return (hypotheses, conclusion, bound_var_ctx)
  else
    let mut new_ctx := bound_var_ctx
    let fvar_ids ← extract_fvars conclusion arg_names
    for (fvar_id, expr) in fvar_ids do
      let fvar := expr.fvarId!
      let fvar_type := bound_var_ctx[fvar_id]!
      new_ctx := new_ctx.insert fvar fvar_type
    let conclusion ← replace_fvars_in_expr conclusion fvar_ids
    let hypotheses ← replace_fvars_in_exprs hypotheses fvar_ids
    return (hypotheses, conclusion, new_ctx)


/-- Takes in the constructor's type, the input variables & their types and the name of the inductive relation,
    and builds an `IRConstructor` containing metadata for the constructor.
    During this process, the names of input arguments (`arg_names`) are unified with variables in the
    conclusion of the constructor. -/
def process_constructor_unify_args (ctor_type: Expr) (input_vars : Array Expr) (input_types : Array Expr)
  (inductive_relation_name: Name) (arg_names : List String) : MetaM IRConstructor := do
  let (bound_vars_and_types, _ , components_of_arrow_type) ← decomposeType ctor_type

  -- `bound_var_ctx` maps free variables (identified by their `FVarId`) to their types
  let mut bound_var_ctx := HashMap.emptyWithCapacity
  for (bound_var, ty) in bound_vars_and_types do
    let fid := FVarId.mk bound_var
    bound_var_ctx := bound_var_ctx.insert fid ty

  match splitLast? components_of_arrow_type with
  | some (hypotheses, conclusion) =>
    let (hypotheses, conclusion, new_ctx) ←
      unify_args_with_conclusion hypotheses conclusion arg_names bound_var_ctx

    let (bound_vars, _) := bound_vars_and_types.unzip
    let (bound_vars_with_base_types, _) :=
      (bound_vars_and_types.filter (fun (_,b) => isBaseType b)).unzip
    let (bound_vars_with_non_base_types, _) :=
      (bound_vars_and_types.filter (fun (_,b) => ¬ isBaseType b)).unzip

    let mut hypotheses_with_only_base_type_args := #[]
    let mut nonlinear_hypotheses := #[]
    let mut hypotheses_that_are_inductive_applications := #[]
    let mut recursive_hypotheses := #[]
    let mut dependencies := #[]

    let conclusion_args := conclusion.getAppArgs
    let final_arg_in_conclusion ← option_to_MetaM conclusion_args.toList.getLast?

    for hyp in hypotheses do
      if ← isDependency hyp.getAppFn inductive_relation_name.getRoot then
        dependencies := dependencies.push hyp.getAppFn
      if hyp.getAppFn.constName == inductive_relation_name then
        recursive_hypotheses := recursive_hypotheses.push hyp
      else if ← allArgsHaveBaseTypes hyp then
        hypotheses_with_only_base_type_args := hypotheses_with_only_base_type_args.push hyp
      else if ← isInductiveRelationApplication hyp then
        hypotheses_that_are_inductive_applications := hypotheses_that_are_inductive_applications.push hyp
      else
        nonlinear_hypotheses := nonlinear_hypotheses.push hyp

    let inp_eq :=  conclusion_args.zip input_vars
    let inp_eq_ztype := inp_eq.zip input_types
    let (num_inp_eq,_) := (inp_eq_ztype.filter (fun (_, t) => isBaseType t)).unzip
    let (notnum_inp_eq,_) := (inp_eq_ztype.filter (fun (_, t) => ¬ isBaseType t)).unzip
    return {
      ctor_expr := ctor_type
      bound_vars := bound_vars,
      bound_var_ctx := new_ctx,
      all_hypotheses := hypotheses,
      conclusion := conclusion,
      conclusion_args := conclusion_args,
      final_arg_in_conclusion := final_arg_in_conclusion
      bound_vars_with_base_types := bound_vars_with_base_types
      hypotheses_with_only_base_type_args := hypotheses_with_only_base_type_args
      bound_vars_with_non_base_types := bound_vars_with_non_base_types
      nonlinear_hypotheses := nonlinear_hypotheses
      hypotheses_that_are_inductive_applications := hypotheses_that_are_inductive_applications
      recursive_hypotheses := recursive_hypotheses
      inp_eq := inp_eq
      num_inp_eq := num_inp_eq
      notnum_inp_eq := notnum_inp_eq
      name_space := inductive_relation_name.getRoot
      dependencies := dependencies
    }
  | none => throwError "Not a match"

/-- Takes in the constructor's type, the input variables & their types and the name of the inductive relation,
    and builds an `IRConstructor` containing metadata for the constructor -/
def process_constructor (ctor_type : Expr) (input_vars: Array Expr) (input_types : Array Expr)
  (inductive_relation_name : Name) : MetaM IRConstructor :=
  process_constructor_unify_args ctor_type input_vars input_types inductive_relation_name []


def arrayppExpr (a: Array Expr) : MetaM (Array Format) := do
  let mut s : Array Format := #[]
  for l in a do
    let o ←  Meta.ppExpr l
    s := s.push o
  return s

def process_constructor_print (pc: IRConstructor) : MetaM Unit := do
  IO.println s!" Vars : {pc.bound_vars}"
  IO.println s!" Cond prop : {pc.all_hypotheses}"
  let op ←  Meta.ppExpr pc.conclusion
  IO.println s!" Out prop:  {op}"
  let oa := arrayppExpr (pc.conclusion_args)
  IO.println s!" Out args:  {← oa}"
  IO.println s!" num_vars : {pc.bound_vars_with_base_types}"
  IO.println s!" num_conds:  {pc.hypotheses_with_only_base_type_args}"
  IO.println s!" notnum_vars : {pc.bound_vars_with_non_base_types}"
  IO.println s!" nonlinear_conds:  {pc.nonlinear_hypotheses}"
  IO.println s!" inductive_conds:  {pc.hypotheses_that_are_inductive_applications}"
  IO.println s!" recursive_conds:  {pc.recursive_hypotheses}"
  IO.println s!" inp eqs:  {pc.inp_eq}"



def mkInpName (n : Nat) := makeInputs_aux  n n
where makeInputs_aux  (n : Nat) (z: Nat) : List String := match n with
| 0 => []
| succ n => ["in" ++ (toString (z - n) )] ++  (makeInputs_aux  n z)

#eval mkInpName 3

#check mkFVarEx

def mkArrayFreshVar (types: Array Expr) : MetaM (Array Expr) :=do
  let mut vars : Array Expr :=#[]
  for i in [:types.size-1] do
    --let type := types[i]!
    let strname := "in" ++ toString (i+1)
    let name := Name.mkStr1 strname
    let var :=   mkFVar ⟨name⟩
    vars := vars.push var
  return vars

/-- Takes in an inductive relation with arguments specified by `arg_names`,
    and extracts metadata corresponding to the `inductive`, returning an `IR_info` -/
def extract_IR_info_with_args (input_expr : Expr) (arg_names : List String) : MetaM IR_info := do
  match input_expr.getAppFn.constName? with
  | some typeName => do
    let type ← inferType input_expr
    let tyexprs_in_arrow_type ← getComponentsOfArrowType type
    -- `hypotheses_types` contains all elements of `tyexprs_in_arrow_type` except the conclusion
    let hypotheses_types := tyexprs_in_arrow_type.pop
    let hypotheses_names := (hypotheses_types.map Expr.constName).pop

    let input_vars ← mkArrayFreshVar hypotheses_types
    let input_vars_names := input_vars.map Expr.name?

    -- `output_type` is the last element (type expression) in the array `hypotheses_types`
    let output_type ← option_to_MetaM (hypotheses_types.back?)
    let output_var ← mkFreshExprMVar output_type (userName:=`out)
    let output_var_name := Expr.name? output_var

    let env ← getEnv
    match env.find? typeName with
    | none => throwError "Type '{typeName}' not found"
    | some (ConstantInfo.inductInfo info) => do
      let mut decomposed_ctor_types : Array DecomposedConstructorType := #[]
      let mut ctors : Array IRConstructor := #[]
      for ctorName in info.ctors do
        let some ctor := env.find? ctorName
         | throwError "IRConstructor '{ctorName}' not found"
        let decomposed_ctor_type ← decomposeType ctor.type
        decomposed_ctor_types := decomposed_ctor_types.push decomposed_ctor_type
        let constructor ←
          if List.isEmpty arg_names then
            process_constructor ctor.type input_vars hypotheses_types typeName
          else
            process_constructor_unify_args ctor.type input_vars hypotheses_types typeName arg_names
        ctors := ctors.push constructor
      let nocond_constructors := ctors.filter (fun x => x.all_hypotheses.size == 0)
      let cond_constructors := ctors.filter (fun x => x.all_hypotheses.size != 0)
      let deps_arr := ctors.map (fun x => x.dependencies)
      let dep_rep := deps_arr.flatten
      let mut dependencies := #[]
      for dep in dep_rep do
        if (! dependencies.contains dep) && (! dep.constName = typeName) then
         dependencies := dependencies.push dep
      return {
        name := typeName
        input_type_names := hypotheses_names,
        output_type_name := Expr.constName output_type
        input_types := hypotheses_types,
        output_type := output_type
        output_vars := output_var
        input_vars := input_vars
        input_var_names := input_vars_names
        output_var_names := output_var_name
        decomposed_ctor_types := decomposed_ctor_types
        constructors := ctors
        nocond_constructors := nocond_constructors
        cond_constructors := cond_constructors
        dependencies:= dependencies
      }
    | some _ =>
      throwError "'{typeName}' is not an inductive type"
  | none => throwError "Not a type"

/-- Takes in an inductive relation and extracts metadata corresponding to the `inductive`,
    returning an `IR_info` -/
def extract_IR_info (input_expr : Expr) : MetaM IR_info :=
  extract_IR_info_with_args input_expr []


def print_constructors (c: Array IRConstructor) : MetaM Unit :=do
  let mut i := 0
  for l in c do
    IO.println s!"IRConstructor {i}: "
    i:= i+1
    process_constructor_print l


def print_relation_info (r: MetaM (IR_info)  ) : MetaM Unit := do
  let relation ← r
  IO.println s!"Relation name: {relation.name}"
  IO.println s!"Input types: {relation.input_types}"
  IO.println s!"Generated type: {relation.output_type}"
  IO.println s!"Input vars: {relation.input_vars}"
  IO.println s!"Out vars: {relation.output_vars}"
  IO.println s!"dependencies: {relation.dependencies}"
  print_constructors relation.constructors



syntax (name := getRelationInfo) "#get_relation" term : command

@[command_elab getRelationInfo]
def elabGetExpr : CommandElab := fun stx => do
  match stx with
  | `(#get_relation $t) =>
    Command.liftTermElabM do
      let e ← elabTerm t none
      let relation := extract_IR_info e
      print_relation_info relation
  | _ => throwError "Invalid syntax"

syntax (name := getRelationInfoChecker) "#get_relation_checker" term : command


#get_relation balanced
#get_relation bst
#get_relation typing



end Plausible.IR
