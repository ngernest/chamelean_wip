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


/-- Determines if an `expr` is an `inductive` relation -/
def is_IR (type : Expr) : MetaM Bool := do
  if ! (← Meta.isInductivePredicate type.constName) then return false
  let ty ← inferType type
  let types ← get_types_chain ty
  let retty := types.toList.getLast!
  return retty.isProp

/-- Determines if an `expr` is a base type (i.e. `Nat, String, Bool`) -/
def is_builtin (n: Expr) : Bool :=
  n.constName ∈ [`Nat, `String, `Bool]

partial def all_args_types (e: Expr) : MetaM (Array Expr) := do
  let args := e.getAppArgs
  if e.isFVar then return #[]
  if args.size = 0 then
    try
      let ty ← inferType e
      if is_builtin e then return #[e] else return ty.getAppArgs
    catch _ => return #[e]
  let mut out : Array Expr := #[]
  for arg in args do
    let arg_types ← all_args_types arg
    out := out.append arg_types
  return out

/-
def is_builtin_cond (e: Expr) : MetaM Bool := do
  let fn := e.getAppFn
  let tys ← all_args_types e
  IO.println s!" expr  : {e}"
  IO.println s!" types  : {tys}"
  if fn.constName! == `Eq then
    let rhs := e.getAppArgs[1]!
    let rhsfun := rhs.getAppFn
    let ty ← inferType rhsfun
    let types := (← get_types_chain ty).pop
    let p := (types.size > 0) ∧ (∀ t ∈ types, is_builtin t)
    return p
  else
    let ty ← inferType fn
    let types := (← get_types_chain ty).pop
    let p := (types.size > 0) ∧ (∀ t ∈ types, is_builtin t)
    return p
-/

def is_builtin_cond (e: Expr) : MetaM Bool := do
  let types ← all_args_types e
  let p := (types.size > 0) ∧ (∀ t ∈ types, is_builtin t)
  return p


def mkFVars (a: Array Name) : Array Expr:= a.map (fun x => mkFVar ⟨x⟩)


def raw_constructor_type := Array (Name × Expr) × Expr × Array Expr
  deriving Repr

/-- The `IRConstructor` type represents a constructor for an inductive relation -/
structure IRConstructor where
  var_names: Array Name
  varid_type : Std.HashMap FVarId Expr
  cond_props: Array Expr
  out_prop: Expr
  output : Expr
  out_args : Array Expr
  num_vars: Array Name
  num_conds: Array Expr
  notnum_vars: Array Name
  recursive_conds: Array Expr
  inductive_conds: Array Expr
  nonlinear_conds: Array Expr
  inp_eq: Array (Expr × Expr)
  ctor_expr: Expr
  num_inp_eq: Array (Expr × Expr)
  notnum_inp_eq: Array (Expr × Expr)
  root: Name
  deriving Repr

/-- A `structure` that bundles together all the metadata for an inductive relation -/
structure IR_info where
  /-- The name of the inductive relation -/
  name : Name
  /-- The names of the types for the input parameters -/
  inp_type_names : Array Name
  out_type_name : Name
  inp_types : Array Expr
  out_type : Expr
  inp_vars: Array Expr
  out_var : Expr
  inp_var_names: Array (Option Name)
  out_var_name : Option Name
  raw_constructors : Array raw_constructor_type
  constructors : Array IRConstructor
  nocond_constructors : Array IRConstructor
  cond_constructors : Array IRConstructor
  deriving Repr

#check Expr.replaceFVarId
#check Expr.fvarsSubset
#check Expr.containsFVar
#check Expr.updateFVar!
#check Expr.applyFVarSubst


def is_pure_inductive_cond (inpexp : Expr) : MetaM Bool := do
  match inpexp.getAppFn.constName? with
  | some typeName => Meta.isInductivePredicate typeName
  | none => return false


def is_inductive_cond (inpexp : Expr) (c: IRConstructor): MetaM Bool := do
  if ! (← is_IR inpexp.getAppFn) then return false
  if inpexp.getAppFn.constName.getRoot == c.root then return true
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


def process_constructor (ctortype: Expr) (inpvar: Array Expr) (inptypes: Array Expr) (relation_name: Name): MetaM IRConstructor := do
  let c ← decompose_type ctortype
  let (list_name_type, _ , list_prop) := c
  let mut varid_type : Std.HashMap FVarId Expr := Std.HashMap.emptyWithCapacity
  for pair in list_name_type do
    let fid:= FVarId.mk pair.1
    varid_type:= varid_type.insert fid pair.2
  match splitLast? list_prop with
  | some (cond_prop, out_prop) =>
    let (var_names, _):= list_name_type.unzip
    let (numvars, _) := (list_name_type.filter (fun (_,b) => is_builtin b)).unzip
    let (notnumvars, _) := (list_name_type.filter (fun (_,b) => ¬ is_builtin b)).unzip
    let mut num_conds := #[]
    let mut nonlinear_conds := #[]
    let mut inductive_conds := #[]
    let mut recursive_conds := #[]
    let outprop_args:= out_prop.getAppArgs
    let output ← option_to_MetaM (out_prop.getAppArgs).toList.getLast?
    for cond in cond_prop do
      if cond.getAppFn.constName = relation_name then
        recursive_conds := recursive_conds.push cond
      else if ← is_builtin_cond cond then
        num_conds := num_conds.push cond
      else if ← is_pure_inductive_cond cond then
        inductive_conds := inductive_conds.push cond
      else
        nonlinear_conds := nonlinear_conds.push cond
    let inp_eq :=  outprop_args.zip inpvar
    let inp_eq_ztype := inp_eq.zip inptypes
    let (num_inp_eq,_) := (inp_eq_ztype.filter (fun (_, t) => is_builtin t)).unzip
    let (notnum_inp_eq,_) := (inp_eq_ztype.filter (fun (_, t) => ¬ is_builtin t)).unzip
    return {
      ctor_expr := ctortype
      var_names := var_names,
      varid_type:= varid_type,
      cond_props:= cond_prop,
      out_prop := out_prop,
      out_args := outprop_args,
      output := output
      num_vars := numvars
      num_conds := num_conds
      notnum_vars := notnumvars
      nonlinear_conds := nonlinear_conds
      inductive_conds := inductive_conds
      recursive_conds := recursive_conds
      inp_eq := inp_eq
      num_inp_eq := num_inp_eq
      notnum_inp_eq := notnum_inp_eq
      root:= relation_name.getRoot
    }
  | none => throwError "Not a match"

def get_Fvar_replist (out_prop: Expr) (inpname: List String) : MetaM (List (FVarId × Expr)) := do
  let new_fvarid : List FVarId := inpname.map (fun x => FVarId.mk (Name.mkStr1 x))
  let new_expr := new_fvarid.map (fun x => Expr.fvar x)
  let args_zip := out_prop.getAppArgs.toList.zip new_expr
  let filter_args_zip:= args_zip.filter (fun x => x.1.isFVar)
  let ret := filter_args_zip.map (fun x => (x.1.fvarId!, x.2))
  return ret

def replace_FVar_list (cond : Expr) (fvarids: List (FVarId × Expr)) : MetaM Expr := do
  let mut newcond := cond
  for rep in fvarids do
    newcond := newcond.replaceFVarId rep.1 rep.2
  return newcond

def replace_arrcond_FVar_list (arrcond : Array Expr) (fvarids: List (FVarId × Expr)) : MetaM (Array Expr) :=
  arrcond.mapM (fun x => replace_FVar_list x fvarids)


def process_constructor_unify_inpname (ctortype: Expr) (inpvar: Array Expr) (inptypes: Array Expr) (relation_name: Name)
                                      (inpname: List String): MetaM IRConstructor := do
  let c ←  decompose_type ctortype
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
    let (numvars, _) := (list_name_type.filter (fun (_,b) => is_builtin b)).unzip
    let (notnumvars, _) := (list_name_type.filter (fun (_,b) => ¬ is_builtin b)).unzip
    let mut num_conds := #[]
    let mut nonlinear_conds := #[]
    let mut inductive_conds := #[]
    let mut recursive_conds := #[]
    let outprop_args:= out_prop.getAppArgs
    let output ← option_to_MetaM (out_prop.getAppArgs).toList.getLast?
    for cond in cond_prop do
      if cond.getAppFn.constName = relation_name then
        recursive_conds := recursive_conds.push cond
      else if ← is_builtin_cond cond then
        num_conds := num_conds.push cond
      else if ← is_pure_inductive_cond cond then
        inductive_conds := inductive_conds.push cond
      else
        nonlinear_conds := nonlinear_conds.push cond
    let inp_eq :=  outprop_args.zip inpvar
    let inp_eq_ztype := inp_eq.zip inptypes
    let (num_inp_eq,_) := (inp_eq_ztype.filter (fun (_, t) => is_builtin t)).unzip
    let (notnum_inp_eq,_) := (inp_eq_ztype.filter (fun (_, t) => ¬ is_builtin t)).unzip
    return {
      ctor_expr := ctortype
      var_names := var_names,
      varid_type:= varid_type,
      cond_props:= cond_prop,
      out_prop := out_prop,
      out_args := outprop_args,
      output := output
      num_vars := numvars
      num_conds := num_conds
      notnum_vars := notnumvars
      nonlinear_conds := nonlinear_conds
      inductive_conds := inductive_conds
      recursive_conds := recursive_conds
      inp_eq := inp_eq
      num_inp_eq := num_inp_eq
      notnum_inp_eq := notnum_inp_eq
      root:= relation_name.getRoot
    }
  | none => throwError "Not a match"


def arrayppExpr (a: Array Expr) : MetaM (Array Format) := do
  let mut s : Array Format := #[]
  for l in a do
    let o ←  Meta.ppExpr l
    s := s.push o
  return s

def process_constructor_print (pc: IRConstructor) : MetaM Unit := do
  IO.println s!" Vars : {pc.var_names}"
  IO.println s!" Cond prop : {pc.cond_props}"
  let op ←  Meta.ppExpr pc.out_prop
  IO.println s!" Out prop:  {op}"
  let oa := arrayppExpr (pc.out_args)
  IO.println s!" Out args:  {← oa}"
  IO.println s!" num_vars : {pc.num_vars}"
  IO.println s!" num_conds:  {pc.num_conds}"
  IO.println s!" notnum_vars : {pc.notnum_vars}"
  IO.println s!" nonlinear_conds:  {pc.nonlinear_conds}"
  IO.println s!" inductive_conds:  {pc.inductive_conds}"
  IO.println s!" recursive_conds:  {pc.recursive_conds}"
  IO.println s!" inp eqs:  {pc.inp_eq}"
  --IO.println s!" var_eqs:  {pc.var_eq}"



def mkInpName (n : Nat) := makeInputs_aux  n n
where makeInputs_aux  (n : Nat) (z: Nat) : List String := match n with
| 0 => []
| succ n => ["in" ++ (toString (z - n) )] ++  (makeInputs_aux  n z)

#eval mkInpName 3

#check mkFVarEx

def mkArrayFreshVar (types: Array Expr) : MetaM (Array Expr) := do
  let mut vars : Array Expr :=#[]
  for i in [:types.size-1] do
    --let type := types[i]!
    let strname := "in" ++ toString (i+1)
    let name := Name.mkStr1 strname
    let var :=   mkFVar ⟨name⟩
    vars := vars.push var
  return vars

def extract_IR_info (inpexp : Expr) : MetaM (IR_info) := do
  match inpexp.getAppFn.constName? with
  | some typeName => do
    let type ← inferType inpexp
    let types_org ← get_types_chain type
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
      let mut raw_constructors : Array raw_constructor_type := #[]
      let mut constructors : Array IRConstructor := #[]
      for ctorName in info.ctors do
        let some ctor := env.find? ctorName
         | throwError "IRConstructor '{ctorName}' not found"
        let raw_constructor ←  decompose_type ctor.type
        raw_constructors:= raw_constructors.push raw_constructor
        let constructor ← process_constructor ctor.type inp_vars types typeName
        constructors:= constructors.push constructor
      let nocond_constructors:= constructors.filter (fun x => (x.cond_props.size = 0))
      let cond_constructors:= constructors.filter (fun x => ¬ (x.cond_props.size = 0))
      return {
        name := typeName
        inp_type_names := names,
        out_type_name := Expr.constName outtype
        inp_types := types,
        out_type := outtype
        out_var := out_var
        inp_vars := inp_vars
        inp_var_names := inp_var_names
        out_var_name := out_var_name
        raw_constructors := raw_constructors
        constructors := constructors
        nocond_constructors := nocond_constructors
        cond_constructors:= cond_constructors
      }
    | some _ =>
      throwError "'{typeName}' is not an inductive type"
  | none => throwError "Not a type"

def extract_IR_info_with_inpname (inpexp : Expr) (inpname: List String) : MetaM (IR_info) := do
  match inpexp.getAppFn.constName? with
  | some typeName => do
    let type ← inferType inpexp
    let types_org ← get_types_chain type
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
      let mut raw_constructors : Array raw_constructor_type := #[]
      let mut constructors : Array IRConstructor := #[]
      for ctorName in info.ctors do
        let some ctor := env.find? ctorName
         | throwError "IRConstructor '{ctorName}' not found"
        let raw_constructor ←  decompose_type ctor.type
        raw_constructors:= raw_constructors.push raw_constructor
        let constructor ← process_constructor_unify_inpname ctor.type inp_vars types typeName inpname
        constructors:= constructors.push constructor
      let nocond_constructors:= constructors.filter (fun x => (x.cond_props.size = 0))
      let cond_constructors:= constructors.filter (fun x => ¬ (x.cond_props.size = 0))
      return {
        name := typeName
        inp_type_names := names,
        out_type_name := Expr.constName outtype
        inp_types := types,
        out_type := outtype
        out_var := out_var
        inp_vars := inp_vars
        inp_var_names := inp_var_names
        out_var_name := out_var_name
        raw_constructors := raw_constructors
        constructors := constructors
        nocond_constructors := nocond_constructors
        cond_constructors:= cond_constructors
      }
    | some _ =>
      throwError "'{typeName}' is not an inductive type"
  | none => throwError "Not a type"



def print_constructors (c: Array IRConstructor) : MetaM Unit := do
  let mut i := 0
  for l in c do
    IO.println s!"IRConstructor {i}: "
    i:= i+1
    process_constructor_print l


def print_relation_info (r: MetaM (IR_info)  ) : MetaM Unit := do
  let relation ← r
  IO.println s!"Relation name: {relation.name}"
  IO.println s!"Input types: {relation.inp_types}"
  IO.println s!"Generated type: {relation.out_type}"
  IO.println s!"Input vars: {relation.inp_vars}"
  IO.println s!"Out vars: {relation.out_var}"
  print_constructors relation.constructors


-- Declare the syntax for the `#get_relation` command (extracts metadata about an inductive relation)
syntax (name := getRelationInfo) "#get_relation" term : command

-- Declare & register the elaborator for `#get_relation`
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
