import Lean
import Std
import Plausible.IR.Example
import Plausible.IR.Prelude
import Lean.Elab.Deriving.DecEq
open Lean.Elab.Deriving.DecEq
open List Nat Array String
open Lean Elab Command Meta Term
open Lean.Parser.Term


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
  bound_var_ctx : Std.HashMap FVarId Expr
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

def is_inductive_cond (inpexp : Expr) (c: IRConstructor): MetaM Bool := do
  if ! (← isInductiveRelation inpexp.getAppFn) then return false
  if inpexp.getAppFn.constName.getRoot == c.name_space then return true
  return false


def isDependency (inpexp : Expr) (ns: Name): MetaM Bool := do
  if ! (← isInductiveRelation inpexp) then return false
  if inpexp.constName.getRoot == ns then return true
  return false

def process_cond_props (cond_prop: Array Expr) (out_prop: Expr) (var_names : Array Name) : MetaM ((Array Expr) × (Array Name) × (Array (Expr × Expr))) := do
  let fvars := var_names.map FVarId.mk
  let mut appeared_fvarid: Array FVarId := #[]
  let mut eq_arr: Array (Expr × Expr) := #[]
  let mut new_arr_expr: Array Expr := #[]
  let mut new_var_names := var_names
  let mut i := 0
  for cond in cond_prop do
    let mut newcond:= cond
    for fv in fvars do
      if cond.containsFVar fv then
        if ¬ appeared_fvarid.contains fv then
          appeared_fvarid := appeared_fvarid.push fv
        else
          if ¬ out_prop.containsFVar fv then
            let newname := Name.mkStr1 (fv.name.toString ++ toString i)
            let newfvarid := FVarId.mk newname
            appeared_fvarid := appeared_fvarid.push newfvarid
            eq_arr:= eq_arr.push (mkFVar fv, mkFVar newfvarid)
            newcond:= newcond.replaceFVarId fv (mkFVar newfvarid)
            new_var_names := new_var_names.push newname
    new_arr_expr:= new_arr_expr.push newcond
  return (new_arr_expr, new_var_names, eq_arr)

/-- Takes in the constructor's type, the input variables & their types and the name of the inductive relation,
    and builds an `IRConstructor` containing metadata for the constructor -/
def process_constructor (ctor_type : Expr) (input_vars: Array Expr) (input_types: Array Expr)
  (inductive_relation_name : Name): MetaM IRConstructor := do
  let (bound_vars_and_types, _ , components_of_arrow_type) ← decomposeType ctor_type

  -- `bound_var_ctx` maps free variables (identified by their `FVarId`) to their types
  let mut bound_var_ctx : Std.HashMap FVarId Expr := Std.HashMap.emptyWithCapacity
  for (bound_var, ty) in bound_vars_and_types do
    let fid := FVarId.mk bound_var
    bound_var_ctx := bound_var_ctx.insert fid ty

  match splitLast? components_of_arrow_type with
  | some (hypotheses, conclusion) =>
    let (bound_vars, _) := bound_vars_and_types.unzip
    let (bound_vars_with_base_types, _) := (bound_vars_and_types.filter (fun (_, ty) => isBaseType ty)).unzip
    let (bound_vars_with_non_base_types, _) := (bound_vars_and_types.filter (fun (_, ty) => !isBaseType ty)).unzip

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
      bound_var_ctx := bound_var_ctx,
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

def get_Fvar_replist (out_prop: Expr) (inpname: List String) : MetaM (List (FVarId × Expr)) :=do
  let new_fvarid : List FVarId := inpname.map (fun x => FVarId.mk (Name.mkStr1 x))
  let new_expr := new_fvarid.map (fun x => Expr.fvar x)
  let args_zip := out_prop.getAppArgs.toList.zip new_expr
  let filter_args_zip:= args_zip.filter (fun x => x.1.isFVar)
  let ret := filter_args_zip.map (fun x => (x.1.fvarId!, x.2))
  return ret

def replace_FVar_list (cond : Expr) (fvarids: List (FVarId × Expr)) : MetaM Expr :=do
  let mut newcond := cond
  for rep in fvarids do
    newcond := newcond.replaceFVarId rep.1 rep.2
  return newcond

def replace_arrcond_FVar_list (arrcond : Array Expr) (fvarids: List (FVarId × Expr)) : MetaM (Array Expr) :=
  arrcond.mapM (fun x => replace_FVar_list x fvarids)


def process_constructor_unify_inpname (ctortype: Expr) (inpvar: Array Expr) (inptypes: Array Expr) (relation_name: Name)
                                      (inpname: List String): MetaM IRConstructor := do
  let c ←  decomposeType ctortype
  let (list_name_type, _ , list_prop) := c
  let mut varid_type : Std.HashMap FVarId Expr := Std.HashMap.emptyWithCapacity
  for pair in list_name_type do
    let fid:= FVarId.mk pair.1
    varid_type:= varid_type.insert fid pair.2
  match splitLast? list_prop with
  | some (cond_prop0, out_prop0) =>
    let replist ← get_Fvar_replist out_prop0 inpname
    for r in replist do
      let inpfvar:= r.2.fvarId!
      let inpfvartype:= varid_type.get! r.1
      varid_type:= varid_type.insert inpfvar inpfvartype
    let out_prop ← replace_FVar_list out_prop0 replist
    let cond_prop ← replace_arrcond_FVar_list cond_prop0 replist
    let (var_names, _):= list_name_type.unzip
    let (numvars, _) := (list_name_type.filter (fun (_,b) => isBaseType b)).unzip
    let (notnumvars, _) := (list_name_type.filter (fun (_,b) => ¬ isBaseType b)).unzip
    let mut num_conds := #[]
    let mut nonlinear_conds := #[]
    let mut inductive_conds := #[]
    let mut recursive_conds := #[]
    let mut dependencies := #[]
    let outprop_args:= out_prop.getAppArgs
    let output ← option_to_MetaM (out_prop.getAppArgs).toList.getLast?
    for cond in cond_prop do
      if ← isDependency cond.getAppFn relation_name.getRoot then
        dependencies := dependencies.push cond.getAppFn
      if cond.getAppFn.constName = relation_name then
        recursive_conds := recursive_conds.push cond
      else if ← allArgsHaveBaseTypes cond then
        num_conds := num_conds.push cond
      else if ← isInductiveRelationApplication cond then
        inductive_conds := inductive_conds.push cond
      else
        nonlinear_conds := nonlinear_conds.push cond
    let inp_eq :=  outprop_args.zip inpvar
    let inp_eq_ztype := inp_eq.zip inptypes
    let (num_inp_eq,_) := (inp_eq_ztype.filter (fun (_, t) => isBaseType t)).unzip
    let (notnum_inp_eq,_) := (inp_eq_ztype.filter (fun (_, t) => ¬ isBaseType t)).unzip
    return {
      ctor_expr := ctortype
      bound_vars := var_names,
      bound_var_ctx:= varid_type,
      all_hypotheses:= cond_prop,
      conclusion := out_prop,
      conclusion_args := outprop_args,
      final_arg_in_conclusion := output
      bound_vars_with_base_types := numvars
      hypotheses_with_only_base_type_args := num_conds
      bound_vars_with_non_base_types := notnumvars
      nonlinear_hypotheses := nonlinear_conds
      hypotheses_that_are_inductive_applications := inductive_conds
      recursive_hypotheses := recursive_conds
      inp_eq := inp_eq
      num_inp_eq := num_inp_eq
      notnum_inp_eq := notnum_inp_eq
      name_space:= relation_name.getRoot
      dependencies:= dependencies
    }
  | none => throwError "Not a match"


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
  --IO.println s!" var_eqs:  {pc.var_eq}"



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

/-- Takes in an inductive relation and extracts metadata corresponding to the `inductive`,
    returning an `IR_info` -/
def extract_IR_info (input_expr : Expr) : MetaM IR_info := do
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
        let constructor ← process_constructor ctor.type input_vars hypotheses_types typeName
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

def extract_IR_info_with_inpname (inpexp : Expr) (inpname: List String) : MetaM (IR_info) := do
  match inpexp.getAppFn.constName? with
  | some typeName => do
    let type ← inferType inpexp
    let types_org ← getComponentsOfArrowType type
    let types := types_org.pop
    let outtype ←  option_to_MetaM (types.back?)
    let names:= (types.map Expr.constName).pop
    let out_var ←   mkFreshExprMVar outtype (userName:=`out)
    let inp_vars ← mkArrayFreshVar types
    let inp_var_names := inp_vars.map Expr.name?
    let out_var_name := Expr.name? out_var
    let env ← getEnv
    match env.find? typeName with
    | none => throwError "Type '{typeName}' not found"
    | some (ConstantInfo.inductInfo info) => do
      let mut raw_constructors : Array DecomposedConstructorType := #[]
      let mut constructors : Array IRConstructor := #[]
      for ctorName in info.ctors do
        let some ctor := env.find? ctorName
         | throwError "IRConstructor '{ctorName}' not found"
        let raw_constructor ←  decomposeType ctor.type
        raw_constructors:= raw_constructors.push raw_constructor
        let constructor ← process_constructor_unify_inpname ctor.type inp_vars types typeName inpname
        constructors:= constructors.push constructor
      let nocond_constructors:= constructors.filter (fun x => (x.all_hypotheses.size = 0))
      let cond_constructors:= constructors.filter (fun x => ¬ (x.all_hypotheses.size = 0))
      let deps_arr := constructors.map (fun x => x.dependencies)
      let dep_rep := deps_arr.flatten
      let mut dependencies := #[]
      for dep in dep_rep do
        if (! dependencies.contains dep) && (! dep.constName = typeName) then
         dependencies:=dependencies.push dep
      return {
        name := typeName
        input_type_names := names,
        output_type_name := Expr.constName outtype
        input_types := types,
        output_type := outtype
        output_vars := out_var
        input_vars := inp_vars
        input_var_names := inp_var_names
        output_var_names := out_var_name
        decomposed_ctor_types := raw_constructors
        constructors := constructors
        nocond_constructors := nocond_constructors
        cond_constructors:= cond_constructors
        dependencies:= dependencies
      }
    | some _ =>
      throwError "'{typeName}' is not an inductive type"
  | none => throwError "Not a type"



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
