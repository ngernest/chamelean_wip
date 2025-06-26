import Lean
import Std
import Plausible.IR.Examples
import Plausible.IR.Prelude
import Lean.Elab.Deriving.DecEq
import Batteries.Data.List.Basic
open Lean.Elab.Deriving.DecEq
open List Nat Array String
open Lean Elab Command Meta Term LocalContext
open Lean.Parser.Term

-- We bring in the `Std` namespace so that we can refer to `HashMap` functions easily
open Std


namespace Plausible.IR

def Array.traverse [Monad M] (f : α → M β) (arr : Array α) : M (Array β) :=
  Array.mapM f arr




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

/-- Determines whether all the arguments to an expression have base types as their type -/
def allArgsHaveBaseTypes (e : Expr) : MetaM Bool := do
  let types ← all_args_types e
  pure $ (types.size > 0) ∧ (∀ t ∈ types, isBaseType t)


def mkFVars (a : Array Name) : Array Expr := a.map (fun x => mkFVar ⟨x⟩)

/-- The type `DecomposedConstructorType` describes a universally-quantified type expression whose body is an arrow type,
     i.e. types of the form `∀ (x1 : τ1) … (xn : τn), Q1 → … → Qn → P`.
    - `DecomposedConstructorType` is a triple containing three components:
    `(#[(x1, τ1), …, (xn, τn)], Q1 → … → Qn → P, #[Q1, …, Qn, P])`.
    - Note: The 2nd component is the body of the forall-expression
    - Note: The 3rd component is an array containing each subterm of the arrow type -/
abbrev DecomposedConstructorType := Array (Name × Expr) × Expr × Array Expr

instance : Repr LocalContext where
  reprPrec lctx a := ""

/-- The datatype `InductiveConstructor` bundles together metadata
    for a constructor of an inductive relation -/
structure InductiveConstructor where
  /-- The type of the constructor, represented as an `Expr` -/
  ctorType : Expr

  /-- Bound variables in the type of the constructor
      (i.e. universally-quantified variables) -/
  bound_vars : Array Name

  /-- Typing context mapping each bound variable to its type -/
  bound_var_ctx : HashMap FVarId Expr

  /-- Bound variables that have base types -/
  bound_vars_with_base_types : Array Name

  /-- Bound variables that have non-base types -/
  bound_vars_with_non_base_types : Array Name

  /-- All the hypotheses for the constructor
     (note that the conclusion is excluded) -/
  all_hypotheses : Array Expr

  /-- All hypotheses that mention the name of the inductive relation -/
  recursive_hypotheses : Array Expr

  /-- Hypotheses where all arguments have base types -/
  hypotheses_with_only_base_type_args : Array Expr

  /-- Hypotheses of the form `R e1 ... en`, where `R` is an inductive relation -/
  hypotheses_that_are_inductive_applications : Array Expr

  /-- Hypotheses in which variables appaer non-linearly (i.e. more than once) -/
  nonlinear_hypotheses : Array Expr

  /-- The conclusion of the constructor, rewritten after
      free variables in the conclusion have been unified with
      the input arguments -/
  conclusion : Expr

  /-- The final argument to the constructor after free variables
      have been rewritten -/
  final_arg_in_conclusion : Expr

  /-- The arguments to the conclusion -/
  conclusion_args : Array Expr

  /-- Maps each argument to the conclusion to the corresponding input variable -/
  inputEqualities: Array (Expr × Expr)
  inputEqs: Array Expr

  /-- `inputEqualities` where the type of the input variable is a base type -/
  baseTypeInputEqualities : Array (Expr × Expr)

  /-- `inputEqualities` where the type of the input variable is *not* a base type -/
  nonBaseTypeInputEqualities : Array (Expr × Expr)

  /-- The namespace in which the inductive relation was defined -/
  name_space : Name

  /-- Expressions `e` that are *dependencies* of the inductive relation
      (i.e. if `e` is an inductive relation that is defined within the current namespace) -/
  dependencies : Array Expr

  LCtx : LocalContext

  deriving Repr

/-- `ToMessageData` instance for polymorphic `HashMap`s
    where the keys implement `Repr` and the values implement `ToMessageData` -/
instance [Repr k] [BEq k] [Hashable k] [ToMessageData v]
  : ToMessageData (HashMap k v) where
  toMessageData hashMap :=
    let entries := hashMap.toList.map fun (key, val) =>
      let kMsg := .ofFormat (repr key)
      let vMsg := toMessageData val
      .compose kMsg (.compose " ↦ " vMsg)
    .bracket "{" (.ofList entries) "}"

instance : ToMessageData InductiveConstructor where
  toMessageData inductiveCtor :=
    let fields := [
      m!"ctorType: {indentD $ inductiveCtor.ctorType}",
      m!"bound_vars: {inductiveCtor.bound_vars}",
      m!"bound_var_ctx: {inductiveCtor.bound_var_ctx}",
      m!"bound_vars_with_base_types: {inductiveCtor.bound_vars_with_base_types}",
      m!"bound_vars_with_non_base_types: {inductiveCtor.bound_vars_with_non_base_types}",
      m!"all_hypotheses: {inductiveCtor.all_hypotheses}",
      m!"recursive_hypotheses: {inductiveCtor.recursive_hypotheses}",
      m!"hypotheses_with_only_base_type_args: {inductiveCtor.hypotheses_with_only_base_type_args}",
      m!"hypotheses_that_are_inductive_applications: {inductiveCtor.hypotheses_that_are_inductive_applications}",
      m!"nonlinear_hypotheses: {inductiveCtor.nonlinear_hypotheses}",
      m!"conclusion: {inductiveCtor.conclusion}",
      m!"final_arg_in_conclusion: {inductiveCtor.final_arg_in_conclusion}",
      m!"conclusion_args: {inductiveCtor.conclusion_args}",
      m!"inputEqualities: {inductiveCtor.inputEqualities}",
      m!"baseTypeInputEqualities: {inductiveCtor.baseTypeInputEqualities}",
      m!"nonBaseTypeInputEqualities: {inductiveCtor.nonBaseTypeInputEqualities}",
      m!"name_space: {inductiveCtor.name_space}",
      m!"dependencies: {inductiveCtor.dependencies}"
    ]
    .bracket "{" (.ofList fields) "}"


/-- The datatype `InductiveInfo` bundles together metadata for an inductive relation -/
structure InductiveInfo where
  /-- The name of the inductive relation -/
  inductive_name : Name

  /-- The names of the inputs to the inductive relation.
      For a relation of the form `P : T1 → … → Tn-1 → Tn → Prop`, the `input_names` are the ames associated
      with `#[T1, …, Tn-1]` -/
  input_names : Array Name

  /-- The types of the inputs to the inductive relation.
      For a relation `P : T1 → … → Tn-1 → Tn → Prop`, the `input_types` are `#[T1, …, Tn-1]` -/
  input_types : Array Expr

  /-- The name of the type for which we wish to generate an inhabitant.
      For a relation `P : T1 → … → Tn-1 → Tn → Prop`, the `output_type_name` is `Tn` -/
  output_type_name : Name

  /-- The type for which we wish to generate an inhabitant.
      For a relation `P : T1 → … → Tn-1 → Tn → Prop`, the `output_type` is `Tn` -/
  output_type : Expr

  /-- The fresh variables correpsonding to the inputs of the inductive relation.
      For a relation of the form `P : T1 → … → Tn-1 → Tn → Prop`,
      the `input_vars` are the variables associated with `#[T1, …, Tn-1]` -/
  input_vars: Array Expr

  /-- The fresh variable names correpsonding to the inputs of the inductive relation.
      For a relation of the form `P : T1 → … → Tn-1 → Tn → Prop`,
      the `input_var_names` are the names associated with `#[T1, …, Tn-1]` -/
  input_var_names: Array Name

  /-- Variable corresponding to the value being generated -/
  output_var : Expr

  /-- Name corresponding to the value being generated -/
  output_var_name : Option Name

  /-- The decomposed types for each constructor of the induction relation.
      See docs for `DecomposedConstructorType` for further details. -/
  decomposed_ctor_types : Array DecomposedConstructorType
  constructors : Array InductiveConstructor
  constructors_with_arity_zero : Array InductiveConstructor
  constructors_with_args : Array InductiveConstructor
  dependencies: Array Expr

  LCtx: LocalContext

/-- Determines if an expression `e` is an application of the form `R e1 ... en`,
    where `R` is an inductive relation  -/
def isInductiveRelationApplication (e : Expr) : MetaM Bool := do
  match e.getAppFn.constName? with
  | some typeName => Meta.isInductivePredicate typeName
  | none => return false

/-- Determines whether an expression `e` is a hypothesis of a constructor `ctor`
   for an inductive relation -/
def isHypothesisOfInductiveConstructor (e : Expr) (ctor : InductiveConstructor) : MetaM Bool := do
  let isIndRel ← isInductiveRelation e.getAppFn
  let exprNamespace := e.getAppFn.constName.getRoot

  if isIndRel || exprNamespace == ctor.name_space then
    return true
  else
    return false

/-- Determines if a hypothesis `hyp` is a recursive call to the inductive relation for which
    `ctor` is a constructor
    (under the hood, this checks that `hyp` and `ctor` are defined in the same namespace) -/
def hypothesisRecursivelyCallsCurrentInductive (hyp : Expr) (ctor : InductiveConstructor) : Bool :=
  hyp.getAppFn.constName.getRoot == ctor.name_space

/-- Determines whether an expression `e` is a dependency of an inductive relation
    (i.e. if `e` is an inductive relation that is defined within the current namespace) -/
def isDependency (e : Expr) (current_namespace : Name) : MetaM Bool := do
  if !(← isInductiveRelation e) then
    return false
  if e.constName.getRoot == current_namespace then
    return true
  return false

/-- Takes each argument in `input_args` and produces a corresponding `FVarId`,
    creates a mapping from that `FVarId` to the `i`-th argument in `conclusion` (if it is an application) -/
def getFVarsMappingInConclusion (conclusion : Expr) (input_args : Array FVarId) : MetaM (Array (FVarId × Expr)) := do
  let new_input_args := Array.map mkFVar input_args
  let conclusion_args_and_new_inputs := Array.zip (conclusion.getAppArgs) new_input_args
  pure $ Array.filterMap (fun (conclusion_arg, new_expr) =>
    if conclusion_arg.isFVar then
      some (conclusion_arg.fvarId!, new_expr)
    else none) conclusion_args_and_new_inputs

/-- Replaces all occurrences of `FVarId`s in `e` using the association list `fvar_ids`, which
    maps each `FVarId` to an `expr` -/
def replace_fvars_in_expr (e : Expr) (fvar_ids : Array (FVarId × Expr)) : MetaM Expr := do
  let mut newcond := e
  for (fvar_id, expr) in fvar_ids do
    newcond := newcond.replaceFVarId fvar_id expr
  return newcond

/-- For each `e` in `exprs_arr`, this function replaces all occurrences of `FVarId`s in `e`
    using the association list `fvar_ids`, which maps each `FVarId` to an `expr` -/
def replace_fvars_in_exprs (exprs_arr : Array Expr) (fvar_ids: Array (FVarId × Expr)) : MetaM (Array Expr) :=
  Array.mapM (fun x => replace_fvars_in_expr x fvar_ids) exprs_arr

/-- Unifies each argument in `arg_names` with each variable in the `conclusion`, returning
    the updated `hypotheses`, `conclusion` and `bound_var_ctx`. If `arg_names` is empty,
    this function just returns `hypotheses`, `conclusion` & `bound_var_ctx` as is. -/
def unify_args_with_conclusion (hypotheses : Array Expr) (conclusion : Expr) (input_args : Array FVarId)
  (bound_var_ctx : HashMap FVarId Expr) : MetaM (Array Expr × Expr × HashMap FVarId Expr) := do
  if Array.isEmpty input_args then
    return (hypotheses, conclusion, bound_var_ctx)
  else
    let mut new_ctx := bound_var_ctx
    let fvar_ids ← getFVarsMappingInConclusion conclusion input_args
    for (fvar_id, expr) in fvar_ids do
      let fvar := expr.fvarId!
      let fvar_type := bound_var_ctx[fvar_id]!
      new_ctx := new_ctx.insert fvar fvar_type
    let conclusion ← replace_fvars_in_expr conclusion fvar_ids
    let hypotheses ← replace_fvars_in_exprs hypotheses fvar_ids
    return (hypotheses, conclusion, new_ctx)

def mkEqs (expr_pairs: Array (Expr × Expr)) (lctx: LocalContext): MetaM (Array Expr) := do withLCtx' lctx do
  let mut eqs := #[]
  for (l,r) in expr_pairs do
    let eq ← mkEq l r
    eqs := eqs.push eq
  return eqs


/-- Takes in the constructor's type, the input variables & their types and the name of the inductive relation,
    and builds an `IRConstructor` containing metadata for the constructor.
    During this process, the names of input arguments (`arg_names`) are unified with variables in the
    conclusion of the constructor. -/
def process_constructor_unify_args (ctor_type: Expr) (input_vars : Array Expr) (input_types : Array Expr)
  (inductive_relation_name: Name) (input_args : Array FVarId) (IRLCtx: LocalContext): MetaM InductiveConstructor := do
  --let (bound_vars_and_types, _ , components_of_arrow_type) ← decomposeType ctor_type
  let (bound_vars_and_types, _ , components_of_arrow_type, ConLCtx) ← decomposeType_withLocalContext ctor_type IRLCtx

  -- `bound_var_ctx` maps free variables (identified by their `FVarId`) to their types
  let mut bound_var_ctx := HashMap.emptyWithCapacity
  for (bound_var, ty) in bound_vars_and_types do
    let fid := FVarId.mk bound_var
    bound_var_ctx := bound_var_ctx.insert fid ty

  match splitLast? components_of_arrow_type with
  | some (hypotheses, conclusion) =>
    let (hypotheses, conclusion, new_ctx) ←
      unify_args_with_conclusion hypotheses conclusion input_args bound_var_ctx

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
    let final_arg_in_conclusion ← Option.getDM (conclusion_args.toList.getLast?)
      (throwError "conclusion_args is an unexpected empty list")

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

    let inputEqualities := conclusion_args.zip input_vars
    let inputEqualitiesWithTypes := inputEqualities.zip input_types
    let (baseTypeInputEqualities, _) := (inputEqualitiesWithTypes.filter (fun (_, ty) => isBaseType ty)).unzip
    let (nonBaseTypeInputEqualities, _) := (inputEqualitiesWithTypes.filter (fun (_, ty) => !isBaseType ty)).unzip

    let inputEqs ←  mkEqs inputEqualities ConLCtx

    return {
      ctorType := ctor_type
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
      inputEqualities := inputEqualities
      baseTypeInputEqualities := baseTypeInputEqualities
      nonBaseTypeInputEqualities := nonBaseTypeInputEqualities
      name_space := inductive_relation_name.getRoot
      dependencies := dependencies
      LCtx := ConLCtx
      inputEqs := inputEqs
    }
  | none => throwError "Not a match"

/-- Takes in the constructor's type, the input variables & their types and the name of the inductive relation,
    and builds an `IRConstructor` containing metadata for the constructor -/
def process_constructor (ctor_type : Expr) (input_vars: Array Expr) (input_types : Array Expr)
  (inductive_relation_name : Name) (IRLCtx: LocalContext): MetaM InductiveConstructor :=
  process_constructor_unify_args ctor_type input_vars input_types inductive_relation_name #[] IRLCtx


def arrayppExpr (a: Array Expr) : MetaM (Array Format) := do
  let mut s : Array Format := #[]
  for l in a do
    let o ←  Meta.ppExpr l
    s := s.push o
  return s

def process_constructor_print (pc: InductiveConstructor) : MetaM Unit := do withLCtx' pc.LCtx do
  IO.println s!" Vars : {pc.bound_vars}"
  IO.println s!" Cond prop : {← Array.mapM Meta.ppExpr pc.all_hypotheses}"
  IO.println s!" Out prop:  {←  Meta.ppExpr pc.conclusion}"
  let oa := arrayppExpr (pc.conclusion_args)
  IO.println s!" Out args:  {← oa}"
  IO.println s!" num_vars : {pc.bound_vars_with_base_types}"
  IO.println s!" num_conds:  {← Array.mapM Meta.ppExpr pc.hypotheses_with_only_base_type_args}"
  IO.println s!" notnum_vars : {pc.bound_vars_with_non_base_types}"
  IO.println s!" nonlinear_conds:  {← Array.mapM Meta.ppExpr pc.nonlinear_hypotheses}"
  IO.println s!" inductive_conds:  {← Array.mapM Meta.ppExpr pc.hypotheses_that_are_inductive_applications}"
  IO.println s!" recursive_conds:  {← Array.mapM Meta.ppExpr pc.recursive_hypotheses}"
  IO.println s!" inp eqs:  {← Array.mapM Meta.ppExpr pc.inputEqs}"



def mkInpName (n : Nat) := makeInputs_aux  n n
where makeInputs_aux  (n : Nat) (z: Nat) : List String := match n with
| 0 => []
| succ n => ["in" ++ (toString (z - n) )] ++  (makeInputs_aux  n z)

/-- Takes an array of input types and generates an array of fresh variable names,
    one for each input -/
def mkArrayFreshVar (input_types : Array Expr) : MetaM (Array Expr) := do
  let mut vars :=#[]
  for i in [:input_types.size-1] do
    let strname := "in" ++ toString (i+1)
    let name := Name.mkStr1 strname
    let var :=  mkFVar ⟨name⟩
    vars := vars.push var
  return vars

def mkInputLocalContext (input_types : Array Expr) (argNames: Array String)
    : MetaM ((Array Expr) × (Array Name) × Expr × Expr × (Array FVarId) × LocalContext) := do
  let mut lctx ← getLCtx
  let mut input_vars := #[]
  let mut input_names := #[]
  let mut input_args := #[]
  for i in [:input_types.size-1] do
    let inpname := Name.mkStr1 ("in" ++ toString (i+1))
    let fvarid ←  mkFreshFVarId
    let var := mkFVar fvarid
    input_vars := input_vars.push var
    input_names := input_names.push inpname
    lctx :=  mkLocalDecl lctx fvarid inpname input_types[i]!
  for (arg, ty) in argNames.zip input_types do
    let argname := Name.mkStr1 arg
    let fvarid ←  mkFreshFVarId
    input_args := input_args.push fvarid
    lctx :=  mkLocalDecl lctx fvarid argname ty
  let output_type ← Option.getDM (input_types.back?) (throwError "unexpected empty input type")
  let outname := Name.mkStr1 "out"
  let fvarid ←  mkFreshFVarId
  let output_var := mkFVar fvarid
  lctx :=  mkLocalDecl lctx fvarid outname output_type
  return (input_vars, input_names, output_var, output_type, input_args, lctx)

/-- Takes in an expression of the form `R e1 ... en`, where `R` is an inductive relation
    with arguments specified by `argNames`, and extracts metadata corresponding to the `inductive`,
    returning an `InductiveInfo` -/
def getInductiveInfoWithArgs (inputExpr : Expr) (argNames : Array String) : MetaM InductiveInfo := do
  match inputExpr.getAppFn.constName? with
  | some inductive_name => do
    let type ← inferType inputExpr
    let tyexprs_in_arrow_type ← getComponentsOfArrowType type

    -- `input_types` contains all elements of `tyexprs_in_arrow_type` except the conclusion (which is `Prop`)
    let input_types := tyexprs_in_arrow_type.pop
    let input_names := (input_types.map Expr.constName).pop

    let (input_vars, input_vars_names, output_var, output_type, input_args, IRLCtx) ← mkInputLocalContext input_types argNames
    --let input_vars_names := input_vars.map Expr.name?

    -- `output_type` is the last element (type expression) in the array `input_types`

    let output_var_name := Expr.name? output_var


    let env ← getEnv
    match env.find? inductive_name with
    | none => throwError "Type '{inductive_name}' not found"
    | some (ConstantInfo.inductInfo info) => do
      let mut decomposed_ctor_types : Array DecomposedConstructorType := #[]
      let mut ctors : Array InductiveConstructor := #[]
      for ctorName in info.ctors do
        let some ctor := env.find? ctorName
         | throwError "IRConstructor '{ctorName}' not found"
        let decomposed_ctor_type ← decomposeType ctor.type
        decomposed_ctor_types := decomposed_ctor_types.push decomposed_ctor_type
        let constructor ←
          if Array.isEmpty argNames then
            process_constructor ctor.type input_vars input_types inductive_name IRLCtx
          else
            process_constructor_unify_args ctor.type input_vars input_types inductive_name input_args IRLCtx
        ctors := ctors.push constructor
      let constructors_with_arity_zero := ctors.filter (fun ctor => ctor.all_hypotheses.size == 0)
      let constructors_with_args := ctors.filter (fun ctor => ctor.all_hypotheses.size != 0)
      let dependencies_arr := Array.flatten $ Array.map (fun x => x.dependencies) ctors
      let mut dependencies := #[]
      for dep in dependencies_arr do
        if (!dependencies.contains dep) && (dep.constName != inductive_name) then
         dependencies := dependencies.push dep
      return {
        inductive_name := inductive_name
        input_names := input_names,
        output_type_name := Expr.constName output_type
        input_types := input_types,
        output_type := output_type
        output_var := output_var
        input_vars := input_vars
        input_var_names := input_vars_names
        output_var_name := output_var_name
        decomposed_ctor_types := decomposed_ctor_types
        constructors := ctors
        constructors_with_arity_zero := constructors_with_arity_zero
        constructors_with_args := constructors_with_args
        dependencies := dependencies
        LCtx := IRLCtx
      }
    | some _ =>
      throwError "'{inductive_name}' is not an inductive type"
  | none => throwError "Not a type"

/-- Takes in an inductive relation and extracts metadata corresponding to the `inductive`,
    returning an `IR_info` -/
def getInductiveInfo (input_expr : Expr) : MetaM InductiveInfo :=
  getInductiveInfoWithArgs input_expr #[]


def print_constructors (ctors : Array InductiveConstructor) : MetaM Unit := do
  let mut i := 0
  for l in ctors do
    IO.println s!"IRConstructor {i}: "
    i := i+1
    process_constructor_print l


/-- Prints the fields of an `inductiveInfo` -/
def print_InductiveInfo (inductiveInfo : InductiveInfo) : MetaM Unit := do withLCtx' inductiveInfo.LCtx do
  IO.println s!"Name of inductive relation: {inductiveInfo.inductive_name}"
  IO.println s!"Input types: {inductiveInfo.input_types}"
  IO.println s!"Type to be generated: {inductiveInfo.output_type}"
  IO.println s!"Input vars: { ← Array.mapM Meta.ppExpr inductiveInfo.input_vars }"
  IO.println s!"Output vars: {← Meta.ppExpr inductiveInfo.output_var}"
  IO.println s!"Dependencies: {inductiveInfo.dependencies}"
  IO.println ""
  print_constructors inductiveInfo.constructors

---------------------------------------------------------------------------------------
-- Command `#get_InductiveInfo` for printing metadata associated with an inductive relation
---------------------------------------------------------------------------------------

syntax (name := getRelationInfo) "#get_InductiveInfo" term : command

@[command_elab getRelationInfo]
def elabGetExpr : CommandElab := fun stx => do
  match stx with
  | `(#get_InductiveInfo $t) =>
    Command.liftTermElabM do
      let e ← elabTerm t none
      let inductiveInfo ← getInductiveInfo e
      print_InductiveInfo inductiveInfo
  | _ => throwError "Invalid syntax"

syntax (name := getRelationInfoChecker) "#get_relation_checker" term : command


-- #get_InductiveInfo balanced
#get_InductiveInfo bst
-- #get_InductiveInfo typing



end Plausible.IR
