import Lean
import Std
import Plausible.IR.Examples
import Plausible.IR.Prelude
import Plausible.New.Idents
import Plausible.IR.KeyValueStore
open List Nat Array String
open Lean Std Elab Command Meta Term LocalContext
open Lean.Parser.Term
open Idents

-- We bring in the `Std` namespace so that we can refer to `HashMap` functions easily
open Std


namespace Plausible.IR

def Array.traverse [Monad M] (f : α → M β) (arr : Array α) : M (Array β) :=
  Array.mapM f arr

/-- `containsNonTrivialFuncApp e inductiveRelationName` determines whether `e` contains a non-trivial function application
    (i.e. a function application where the function name is *not* the same as `inductiveRelationName`,
    and where the function is also *not* a constructor of an inductive data type) -/
def containsNonTrivialFuncApp (e : Expr) (inductiveRelationName : Name) : MetaM Bool := do
  -- Helper function to check whether a sub-term is a non-trivial function application
  let rec checkSubTerm (subExpr : Expr) : MetaM Bool :=
    if subExpr.isApp then
      let fn := subExpr.getAppFn
      if fn.isConst then
        let constName := fn.constName!
        if constName.getRoot != inductiveRelationName then do
          let info ← getConstInfo constName
          return !info.isCtor
        else
          return false
      else
        return false
    else
      return false

  match e with
  | .app f arg =>
    if (← checkSubTerm f)
      then return true
    else
      checkSubTerm arg
  | .lam _ _ body _ => checkSubTerm body
  | .forallE _ _ body _ => checkSubTerm body
  | .letE _ _ value body _ => do
    if (← checkSubTerm value) then
      return true
    else
      checkSubTerm body
  | .mdata _ expr => checkSubTerm expr
  | .proj _ _ struct => checkSubTerm struct
  | _ => return false


/-- Determines whether a type expression is an inductive relation -/
def isInductiveRelation (tyexpr : Expr) : MetaM Bool := do
  if ! (← Meta.isInductivePredicate tyexpr.constName) then
    return false
  let ty ← inferType tyexpr
  let arrow_type_components ← getComponentsOfArrowType ty
  -- Return type must be `Prop` in order for `tyexpr` to be an inductive relation
  let return_type := arrow_type_components.toList.getLast!
  return return_type.isProp

/-- `rewriteFuncCallsInConclusion hypotheses conclusion inductiveRelationName` does the following:
    1. Checks if the `conclusion` contains a function call where the function is *not* the same as the `inductiveRelationName`.
       (If no, we just return the pair `(hypotheses, conclusion)` as is.)
    2. If yes, we create a fresh variable & add an extra hypothesis where the fresh var is bound to the result of the function call.
    3. We then rewrite the conclusion, replacing occurrences of the function call with the fresh variable,
    The updated hypotheses & conclusion are subsequently returned.
    - Note: it is the caller's responsibility to check that `conclusion` does indeed contain
      a non-trivial function application (e.g. by using `containsNonTrivialFuncApp`) -/
def rewriteFuncCallsInConclusion (hypotheses : Array Expr) (conclusion : Expr) (inductiveRelationName : Name) : MetaM (Array Expr × Expr) :=

  -- Filter out cases where the function being called is the same as the inductive relation's name
  -- Note: this analysis is more simplistic compared to the one performed by `containsNonTrivialFuncApp`,
  -- which is why callers should have called `containsNonTrivialFuncApp` beforehand
  let possibleFuncApp := Expr.find? (fun subExpr =>
    subExpr.isApp && subExpr.getAppFn.constName.getRoot != inductiveRelationName) conclusion

  match possibleFuncApp with
  | none => return (hypotheses, conclusion)
  | some funcAppExpr => do
    let funcAppType ← inferType funcAppExpr

    -- We use `withLocalDecl` to add the fresh variable to the local context
    withLocalDeclD `unknown funcAppType (fun newVarExpr => do
      -- Create a new hypothesis stating that `newVarExpr = funcAppExpr`, then
      -- add it to the array of `hypotheses`
      let newHyp ← mkEq newVarExpr funcAppExpr
      -- let newVarFVarId := newVarExpr.fvarId!
      let updatedHypotheses := Array.push hypotheses newHyp

      -- Note: since we're doing a purely syntactic rewriting operation here,
      -- it suffices to use `==` to compare `subExpr` with `funcAppExpr` instead of using `MetaM.isDefEq`
      let rewrittenConclusion := Expr.replace
        (fun subExpr => if subExpr == funcAppExpr then some newVarExpr else none) conclusion

      -- Insert the fresh variable into the bound-variable context
      return (updatedHypotheses, rewrittenConclusion))

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


/-- The type `DecomposedConstructorType` describes a universally-quantified type expression whose body is an arrow type,
     i.e. types of the form `∀ (x1 : τ1) … (xn : τn), Q1 → … → Qn → P`.
    - `DecomposedConstructorType` is a triple containing three components:
    `(#[(x1, τ1), …, (xn, τn)], Q1 → … → Qn → P, #[Q1, …, Qn, P])`.
    - Note: The 2nd component is the body of the forall-expression
    - Note: The 3rd component is an array containing each subterm of the arrow type -/
abbrev DecomposedConstructorType := Array (Name × Expr) × Expr × Array Expr

/-- Simple `Repr` instance for `LocalContext` -/
instance : Repr LocalContext where
  reprPrec lctx _ :=
    let decls := lctx.decls.toList.filterMap id
    if decls.isEmpty then
      "⟨⟩"
    else
      let declReprs := decls.map fun decl =>
        let name := decl.userName
        let type := decl.type
        match decl.kind with
        | .default => s!"{name} : {type}"
        | .auxDecl => s!"{name} : {type} (aux)"
        | .implDetail => s!"{name} : {type} (impl)"
      let inner := String.intercalate ", " declReprs
      Std.Format.bracket "⟨" (Std.Format.text inner) "⟩"

/-- The datatype `InductiveConstructor` bundles together metadata
    for a constructor of an inductive relation -/
structure InductiveConstructor where
  /-- The name of the constructor, represented as an `Expr` -/
  ctorName : Name

  /-- The type of the constructor, represented as an `Expr` -/
  ctorType : Expr

  /-- Input variables -/
  input_vars : Array Expr

  /-- Constructor Expr -/
  ctorExpr : Expr

  /-- Bound variables in the type of the constructor
      (i.e. universally-quantified variables) -/
  bound_vars : Array Name

  /-- Unification map between bound variables in conclusion and input_vars -/
  inputVarsToConclusionArgsMap : Array (Expr × Expr)

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

  localCtx : LocalContext

/-- The datatype `InductiveInfo` bundles together metadata for an inductive relation -/
structure InductiveInfo where
  /-- The name of the inductive relation -/
  inductive_name : Name

  /-- The types of the inputs to the inductive relation.
      For a relation `P : T1 → … → Tn-1 → Tn → Prop`, the `input_types` are `#[T1, …, Tn-1]` -/
  input_types : Array Expr

  /-- The fresh variables correpsonding to the inputs of the inductive relation.
      For a relation of the form `P : T1 → … → Tn-1 → Tn → Prop`,
      the `input_vars` are the variables associated with `#[T1, …, Tn-1]` -/
  input_vars: Array Expr

  /-- The fresh variable names correpsonding to the inputs of the inductive relation.
      For a relation of the form `P : T1 → … → Tn-1 → Tn → Prop`,
      the `input_var_names` are the names associated with `#[T1, …, Tn-1]` -/
  input_var_names: Array Name

  /-- The decomposed types for each constructor of the induction relation.
      See docs for `DecomposedConstructorType` for further details. -/
  decomposed_ctor_types : Array DecomposedConstructorType
  constructors : Array InductiveConstructor
  constructors_with_arity_zero : Array InductiveConstructor
  constructors_with_args : Array InductiveConstructor
  dependencies: Array Expr

  /-- The `LocalContext` associated with the inductive relation -/
  localCtx : LocalContext

  /-- A `HashMap` mapping argument names to freshened versions of the same name
      (the other `LocalContext` field in `InductiveInfo` only stores the freshened version) -/
  nameMap : HashMap Name Name

/-- Determines if an expression `e` is an application of the form `R e1 ... en`,
    where `R` is an inductive relation  -/
def isInductiveRelationApplication (e : Expr) : MetaM Bool := do
  match e.getAppFn.constName? with
  | some typeName => Meta.isInductivePredicate typeName
  | none => return false

/-- Determines whether an expression `e` is a hypothesis of a constructor `ctor`
   for an inductive relation -/
def isHypothesisOfInductiveConstructor_inNamespace (e : Expr) (namesp : Name) : MetaM Bool := do
  let isIndRel ← isInductiveRelation e.getAppFn
  let exprNamespace := e.getAppFn.constName.getRoot
  let allbasedtype ← allArgsHaveBaseTypes e
  if ! isIndRel then
    return false
  else if allbasedtype && exprNamespace != namesp then
    return false
  else return true


/-- Determines whether an expression `e` is a hypothesis of a constructor `ctor`
   for an inductive relation -/
def isHypothesisOfInductiveConstructor (e : Expr) (ctor : InductiveConstructor) : MetaM Bool :=
  isHypothesisOfInductiveConstructor_inNamespace e ctor.name_space


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
def replaceFVarInExpr (e : Expr) (fvar_ids : Array (FVarId × Expr)) : MetaM Expr := do
  let mut newcond := e
  for (fvar_id, expr) in fvar_ids do
    newcond := newcond.replaceFVarId fvar_id expr
  return newcond

/-- For each `e` in `exprs_arr`, this function replaces all occurrences of `FVarId`s in `e`
    using the association list `fvar_ids`, which maps each `FVarId` to an `expr` -/
def replaceFVarsInExprs (exprs_arr : Array Expr) (fvar_ids: Array (FVarId × Expr)) : MetaM (Array Expr) :=
  Array.mapM (fun x => replaceFVarInExpr x fvar_ids) exprs_arr

/-- Unifies each argument in `arg_names` with each variable in the `conclusion`, returning
    the updated `hypotheses`, `conclusion` and `input_args`. If `arg_names` is empty,
    this function just returns `hypotheses`, `conclusion` & `input_args` as is. -/
def unifyArgsWithConclusion (hypotheses : Array Expr) (conclusion : Expr) (input_args : Array FVarId)
    : MetaM (Array Expr × Expr × Array (Expr × Expr)) := do
  if Array.isEmpty input_args then
    return (hypotheses, conclusion, #[])
  else
    let fvar_ids ← getFVarsMappingInConclusion conclusion input_args
    let conclusion ← replaceFVarInExpr conclusion fvar_ids
    let hypotheses ← replaceFVarsInExprs hypotheses fvar_ids
    let mapping := fvar_ids.map fun (id, exp2) => (mkFVar id, exp2)
    return (hypotheses, conclusion, mapping)


/-- Takes in the constructor's type, the input variables & their types and the name of the inductive relation,
    and builds an `IRConstructor` containing metadata for the constructor.
    During this process, the names of input arguments (`argNames`) are unified with variables in the
    conclusion of the constructor. -/
def processConstructorUnifyArgs (ctorName : Name) (ctorType: Expr) (inputVars : Array Expr) (inputTypes : Array Expr)
  (inductiveRelationName: Name) (localCtx: LocalContext): MetaM InductiveConstructor := do
  let (bound_vars_and_types, ctorExpr, components_of_arrow_type, ctorLocalCtx) ← decomposeTypeWithLocalContext ctorType localCtx

  let inputFVarIds := inputVars.map Expr.fvarId!
  match splitLast? components_of_arrow_type with
  | some (originalHypotheses, originalConclusion) =>
    -- Check if `conclusion` contains any subterms that are function calls
    -- If yes, rewrite the function calls using `rewriteFuncCallsInConclusion`
    -- Then, unify `argNames` with each arg in the conclusion
    let (hypotheses, conclusion, newCtx) ←
      if (← containsNonTrivialFuncApp originalConclusion inductiveRelationName) then
        let (updatedHypotheses, rewrittenConclusion) ←
          rewriteFuncCallsInConclusion originalHypotheses originalConclusion inductiveRelationName
        unifyArgsWithConclusion updatedHypotheses rewrittenConclusion inputFVarIds
      else
        unifyArgsWithConclusion originalHypotheses originalConclusion inputFVarIds

    let (bound_vars, _) := bound_vars_and_types.unzip
    let (bound_vars_with_base_types, _) :=
      (bound_vars_and_types.filter (fun (_, b) => isBaseType b)).unzip
    let (bound_vars_with_non_base_types, _) :=
      (bound_vars_and_types.filter (fun (_, b) => ¬ isBaseType b)).unzip

    let mut hypotheses_with_only_base_type_args := #[]
    let mut nonlinear_hypotheses := #[]
    let mut hypotheses_that_are_inductive_applications := #[]
    let mut recursive_hypotheses := #[]
    let mut dependencies := #[]

    let conclusion_args := conclusion.getAppArgs
    let final_arg_in_conclusion ← Option.getDM (conclusion_args.toList.getLast?)
      (throwError "conclusion_args is an unexpected empty list")

    for hyp in hypotheses do
      if ← isHypothesisOfInductiveConstructor_inNamespace hyp inductiveRelationName.getRoot then
        hypotheses_that_are_inductive_applications := hypotheses_that_are_inductive_applications.push hyp
      if ← isDependency hyp.getAppFn inductiveRelationName.getRoot then
        dependencies := dependencies.push hyp.getAppFn
      if hyp.getAppFn.constName == inductiveRelationName then
        recursive_hypotheses := recursive_hypotheses.push hyp
      else if ← allArgsHaveBaseTypes hyp then
        hypotheses_with_only_base_type_args := hypotheses_with_only_base_type_args.push hyp
      else
        nonlinear_hypotheses := nonlinear_hypotheses.push hyp

    let inputEqualities := conclusion_args.zip inputVars

    let inputEqualitiesWithTypes := inputEqualities.zip inputTypes
    let (baseTypeInputEqualities, _) := (inputEqualitiesWithTypes.filter (fun (_, ty) => isBaseType ty)).unzip
    let (nonBaseTypeInputEqualities, _) := (inputEqualitiesWithTypes.filter (fun (_, ty) => !isBaseType ty)).unzip

    let inputEqs ← mkExprEqualities inputEqualities ctorLocalCtx

    return {
      ctorType := ctorType
      ctorName := ctorName
      ctorExpr := ctorExpr
      input_vars := inputVars,
      bound_vars := bound_vars,
      inputVarsToConclusionArgsMap := newCtx,
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
      name_space := inductiveRelationName.getRoot
      dependencies := dependencies
      localCtx := ctorLocalCtx
      inputEqs := inputEqs
    }
  | none => throwError "Not a match"

def constructor_header (con: InductiveConstructor) : MetaM String := withLCtx' con.localCtx do
  return toString (con.ctorName) ++ " : " ++  toString (← Meta.ppExpr con.ctorExpr)

def process_constructor_print (pc: InductiveConstructor) : MetaM Unit := withLCtx' pc.localCtx do
  IO.println s!" Constructor Expr : {← Meta.ppExpr pc.ctorExpr}"
  IO.println s!" Input Vars : {← Array.mapM Meta.ppExpr pc.input_vars}"
  IO.println s!" Bound Vars : {pc.bound_vars}"
  IO.println s!" Input maps : {(← Array.mapM Meta.ppExpr pc.inputVarsToConclusionArgsMap.unzip.1).zip (← Array.mapM Meta.ppExpr pc.inputVarsToConclusionArgsMap.unzip.2)}"
  IO.println s!" Cond props : {← Array.mapM Meta.ppExpr pc.all_hypotheses}"
  IO.println s!" Conclusion prop :  {← Meta.ppExpr pc.conclusion}"
  IO.println s!" Builtin-typed vars : {pc.bound_vars_with_base_types}"
  IO.println s!" Non-builtin-typed vars : {pc.bound_vars_with_non_base_types}"
  IO.println s!" Builtin-typed props :  {← Array.mapM Meta.ppExpr pc.hypotheses_with_only_base_type_args}"
  --IO.println s!" nonlinear_conds:  {← Array.mapM Meta.ppExpr pc.nonlinear_hypotheses}"
  IO.println s!" Inductive_conds:  {← Array.mapM Meta.ppExpr pc.hypotheses_that_are_inductive_applications}"
  IO.println s!" Recursive_conds:  {← Array.mapM Meta.ppExpr pc.recursive_hypotheses}"
  IO.println s!" Input eqs:  {← Array.mapM Meta.ppExpr pc.inputEqs}"


def print_constructors (ctors : Array InductiveConstructor) : MetaM Unit := do
  let mut i := 0
  for l in ctors do
    IO.println s!"IRConstructor {i}: "
    i := i+1
    process_constructor_print l

/-- Helper function for creating `n` names -/
def mkDefaultInputNames_aux (n: Nat) : MetaM (Array String) := do
  let mut input_names := #[]
  for i in [:n] do
    let inpname := "in" ++ toString (i+1)
    input_names := input_names.push inpname
  return input_names

/-- Creates an array of default names corresponding to the function that appears
    in `inputExpr`

    (precondition: `inputExpr` should be a function application) -/
def mkDefaultInputNames (inputExpr : Expr) : MetaM (Array String) := do
  match inputExpr.getAppFn.constName? with
  | some _ => do
    let type ← inferType inputExpr
    let tyexprs_in_arrow_type ← getComponentsOfArrowType type
    let input_types := tyexprs_in_arrow_type.pop
    return (← mkDefaultInputNames_aux input_types.size)
  | none => throwError "input expression is not a function application"

/-- `mkInitialContextForInductiveRelation inputTypes inputNames`
    creates the initial `LocalContext` where each `(x, τ)` in `Array.zip inputTypes inputNames`
    is given the declaration `x : τ` in the resultant context.

    This function returns a triple containing `inputTypes`, `inputNames` represented as an `Array` of `Name`s,
    and the resultant `LocalContext`. -/
def mkInitialContextForInductiveRelation (inputTypes : Array Expr) (inputNameStrings : Array String) : MetaM (Array Expr × Array Name × LocalContext × HashMap Name Name) := do
  let inputNames := Name.mkStr1 <$> inputNameStrings
  let localDecls := inputNames.zip inputTypes
  withLocalDeclsDND localDecls $ fun exprs => do
    let mut nameMapBindings := #[]
    let mut localCtx ← getLCtx
    for currentName in inputNames do
      let freshName := getUnusedName localCtx currentName
      localCtx := renameUserName localCtx currentName freshName
      nameMapBindings := nameMapBindings.push (currentName, freshName)
    let nameMap := HashMap.ofList (Array.toList nameMapBindings)
    return (exprs, inputNames, localCtx, nameMap)


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

    let (input_vars, input_vars_names, localCtx, nameMap) ← mkInitialContextForInductiveRelation input_types argNames

    let env ← getEnv
    match env.find? inductive_name with
    | none => throwError "Type '{inductive_name}' not found"
    | some (ConstantInfo.inductInfo info) => do
      let mut decomposed_ctor_types := #[]
      let mut ctors := #[]
      for ctorName in info.ctors do
        let some ctor := env.find? ctorName
         | throwError "IRConstructor '{ctorName}' not found"
        let decomposed_ctor_type ← decomposeType ctor.type
        decomposed_ctor_types := decomposed_ctor_types.push decomposed_ctor_type
        let constructor ←
            processConstructorUnifyArgs ctorName ctor.type input_vars input_types inductive_name localCtx
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
        input_types := input_types,
        input_vars := input_vars
        input_var_names := input_vars_names
        decomposed_ctor_types := decomposed_ctor_types
        constructors := ctors
        constructors_with_arity_zero := constructors_with_arity_zero
        constructors_with_args := constructors_with_args
        dependencies := dependencies
        localCtx := localCtx
        nameMap := nameMap
      }
    | some _ =>
      throwError s!"{inductive_name} is not an inductive relation"
  | none => throwError s!"{inputExpr} is not a type"

/-- Takes in an inductive relation and extracts metadata corresponding to the `inductive`,
    returning an `IR_info` -/
def getInductiveInfo (input_expr : Expr) : MetaM InductiveInfo := do
  let inp_names ← mkDefaultInputNames input_expr
  getInductiveInfoWithArgs input_expr inp_names


/-- Prints the fields of an `inductiveInfo` -/
def print_InductiveInfo (inductiveInfo : InductiveInfo) : MetaM Unit := withLCtx' inductiveInfo.localCtx do
  IO.println s!"Name of inductive relation: {inductiveInfo.inductive_name}"
  IO.println s!"Input types: {inductiveInfo.input_types}"
  IO.println s!"Input vars: { ← Array.mapM Meta.ppExpr inductiveInfo.input_vars }"
  IO.println s!"Dependencies: {inductiveInfo.dependencies}"
  IO.println ""
  print_constructors inductiveInfo.constructors

---------------------------------------------------------------------------------------
-- Command `#get_InductiveInfo` for printing metadata associated with an inductive relation
---------------------------------------------------------------------------------------

syntax (name := getRelationInfo) "#get_InductiveInfo" term : command

@[command_elab getRelationInfo]
def elabGetIRInfo : CommandElab := fun stx => do
  match stx with
  | `(#get_InductiveInfo $t) =>
    Command.liftTermElabM do
      let e ← elabTerm t none
      let inductiveInfo ← getInductiveInfo e
      print_InductiveInfo inductiveInfo
  | _ => throwError "Invalid syntax"


syntax (name := getRelationInfoWithName) "#get_InductiveInfo" term "with_name" term : command

@[command_elab getRelationInfoWithName]
def elabGetIRInfoWithName : CommandElab := fun stx => do
  match stx with
  | `(#get_InductiveInfo $t with_name $t2:term) =>
    Command.liftTermElabM do
      let e ← elabTerm t none
      let inpname ← termToStringList t2
      let inductiveInfo ← getInductiveInfoWithArgs e inpname.toArray
      print_InductiveInfo inductiveInfo
  | _ => throwError "Invalid syntax"


end Plausible.IR
