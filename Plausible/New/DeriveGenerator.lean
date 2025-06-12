import Lean
import Std
import Plausible.New.GenOption
import Plausible.IR.Prelude
import Plausible.IR.Constructor
import Plausible.IR.GCCall
import Plausible.Gen
import Plausible.New.OptionTGen
import Plausible.New.Constraints
import Plausible.New.Idents

open Plausible.IR
open Lean Elab Command Meta Term Parser Std
open Idents

/-- Extracts the name of the induction relation and its arguments -/
def parseInductiveApp (body : Term) : CommandElabM (Name × TSyntaxArray `term) := do
  match body with
  | `($indRel:ident $args:term*) => do
    return (indRel.getId, args)
  | `($indRel:ident) => do
    return (indRel.getId, #[])
  | _ => throwErrorAt body "Expected inductive type application"

/-- Extracts the name of the induction relation and its arguments
    (variant of `parseInductiveApp` that returns the name of the
    inductive relation as a `TSyntax term` instead of a `Name`,
    and the arguments to the `inductive` as an `Array` of `TSyntax term`s ) -/
def deconstructInductiveApplication (body : Term) : CommandElabM (TSyntax `term × Array (TSyntax `term)) := do
  match body with
  | `($indRel:ident $args:term*) =>
    return (indRel, args)
  | `($indRel:ident) =>
    return (indRel, #[])
  | _ => throwError "Expected inductive type application"

/-- Extracts the name of a parameter from a corresponding `Term`.
    If this is not possible, a fresh user-facing name is produced. -/
def extractParamName (arg : Term) : MetaM Name :=
  match arg with
  | `($name:ident) => pure name.getId
  | _ => Core.mkFreshUserName `param

/-- Analyzes the type of the inductive relation and matches each
    argument with its expected type, returning an array of
    (parameter name, type expression) pairs -/
def analyzeInductiveArgs (inductiveName : Name) (args : Array Term) :
  CommandElabM (Array (Name × TSyntax `term)) := do

  -- Extract the no. of parameters & indices for the inductive
  let inductInfo ← getConstInfoInduct inductiveName
  let numParams := inductInfo.numParams
  let numIndices := inductInfo.numIndices
  let numArgs := numParams + numIndices

  if args.size != numArgs then
    throwError s!"Expected {numArgs} arguments but received {args.size} arguments instead"

  -- Extract the type of the inductive relation
  let inductType := inductInfo.type

  liftTermElabM $
    forallTelescope inductType (fun xs _ => do
      let mut paramInfo : Array (Name × TSyntax `term) := #[]

      for i in [:args.size] do
        -- Match each argument with its expected type
        let arg := args[i]!
        let paramFVar := xs[i]!
        let paramType ← inferType paramFVar

        -- Extract parameter name from the argument syntax
        let paramName ← extractParamName arg

        -- Use Lean's delaborator to express the parameter type
        -- using concrete surface-level syntax
        let typeSyntax ← PrettyPrinter.delab paramType

        paramInfo := paramInfo.push (paramName, typeSyntax)

      pure paramInfo)


/-- Determines if a constructor for an inductive relation is *recursive*
    (i.e. the constructor's type mentions the inductive relation)
    - Note: this function only considers constructors with arrow types -/
def isConstructorRecursive (inductiveName : Name) (ctorName : Name) : MetaM Bool := do
  let ctorInfo ← getConstInfo ctorName
  let ctorType := ctorInfo.type

  let (_, _, type_exprs_in_arrow_type) ← decomposeType ctorType
  match splitLast? type_exprs_in_arrow_type with
  | some (hypotheses, _conclusion) =>
    for hyp in hypotheses do
      if hyp.getAppFn.constName == inductiveName then
        return true
    return false
  | none => throwError "constructors with non-arrow types are not-considered to be recursive"

/-- Produces a generator for a constructor identified by its name (`ctorName`),
    where `targetIdx` is the index of the constructor argument whose value we wish to generate -/
def getGeneratorForTarget (ctorName : Name) (targetIdx : Nat) : MetaM (TSyntax `term) := do
  let _lctx ← getLCtx

  let ctorInfo ← getConstInfo ctorName
  let ctorType := ctorInfo.type

  let (bound_vars_and_types, _, type_exprs_in_arrow_type) ← decomposeType ctorType

  -- `bound_var_ctx` maps free variables (identified by their `FVarId`) to their types
  let mut bound_var_ctx := HashMap.emptyWithCapacity
  for (bound_var, ty) in bound_vars_and_types do
    let fid := FVarId.mk bound_var
    bound_var_ctx := bound_var_ctx.insert fid ty

  match splitLast? type_exprs_in_arrow_type with
  | some (_hypotheses, conclusion) =>
    logInfo s!"conclusion = {conclusion}"


    -- Find the argument (an `Expr`) corresponding to the value we wish to generate,
    -- then delaborate it to a `Term`
    let conclusionArgs := conclusion.getAppArgs
    let mut _conclusionArgsFVars := #[]
    for arg in conclusionArgs do
      let argFVars ← extractFVarsMetaM arg
      _conclusionArgsFVars := Array.appendUniqueElements _conclusionArgsFVars argFVars

    let targetArg := conclusionArgs[targetIdx]!
    let targetArgFVars ← extractFVarsMetaM targetArg

    _conclusionArgsFVars := Array.removeAll _conclusionArgsFVars targetArgFVars

    -- -- Note: generatorCalls is empty for some reason
    -- let mut generatorCalls := #[]
    -- for fvar in conclusionArgsFVars do
    --   let ty := bound_var_ctx.get! fvar
    --   let tyTerm ← PrettyPrinter.delab ty
    --   -- Note: this line complains for the BST example because `lo` is a free variable
    --   -- that doesn't appear in the `localContext`
    --   let fvarName ← Lean.mkIdent <$> FVarId.getUserName fvar
    --   let expr ← `(doSeq| let $fvarName:term ← $interpSampleFn:term $tyTerm)
    --   generatorCalls := generatorCalls.push expr

    -- logInfo s!"generatorCalls = {generatorCalls}"

    -- let generatorCallsArray := TSyntaxArray.mk generatorCalls
    -- let doBlockBody ← `(doSeq| $generatorCallsArray* )
    -- let generatorBody ← `(fun _ => do $doBlockBody)

    let argToGenTerm ← PrettyPrinter.delab targetArg
    let generatorBody ← `(fun _ => $pureIdent $argToGenTerm)

    `((1, $thunkGenFn ($generatorBody)))

  | none => throwError s!"Constructor {ctorName} has type {ctorType} which can't be decomposed"

/-- Produces the names of all non-recursive constructors of an inductive relation.
    A constructor is considered non-recursive if:
    - It is *not* an arrow type (i.e. it can be used directly to build an inhabitant of the inductive relation)
    - It is an arrow type but all the arrow type's components are non-recursive -/
def findNonRecursiveConstructors (inductiveName : Name) : MetaM (Array Name) := do
  let inductInfo ← getConstInfoInduct inductiveName
  let allConstructors := inductInfo.ctors

  let mut nonRecursive : Array Name := #[]

  for ctorName in allConstructors do
    let isRec ← isConstructorRecursive inductiveName ctorName
    if !isRec then
      nonRecursive := nonRecursive.push ctorName

  return nonRecursive

/-- Finds the index of the argument in the inductive application for the value we wish to generate
    (i.e. finds `i` s.t. `args[i] == targetVar`) -/
def findTargetVarIndex (targetVar : Name) (args : TSyntaxArray `term) : Option Nat :=
  Array.findIdx? (fun arg => arg.getId == targetVar) (TSyntaxArray.raw args)


/-- Produces the actual generator function.
    - `inductiveName` is the name of the inductive relation
    - `targetVar`, `targetType`: the variable name and type of the value to be generated
    - `args`: the other arguments to the inductive relation -/
def mkGeneratorFunction (inductiveName : Name) (targetVar : Name) (targetTypeSyntax : TSyntax `term)
  (args : TSyntaxArray `term) : CommandElabM (TSyntax `command) := do

  -- Fetch the ambient local context, which we need to generate user-facing fresh names
  -- that are accessible to the user
  let localCtx ← liftTermElabM $ getLCtx

  -- Extract the names of the constructors for the inductive
  let inductInfo ← getConstInfoInduct inductiveName
  let _constructorNames := inductInfo.ctors

  -- Find the index of the argument in the inductive application for the value we wish to generate
  -- (i.e. find `i` s.t. `args[i] == targetVar`)
  let targetIdxOpt := findTargetVarIndex targetVar args
  if let .none := targetIdxOpt then
    throwError "cannot find index of value to be generated"
  let targetIdx := Option.get! targetIdxOpt

  -- Find the names of all non-recursive constructors
  let nonRecursiveConstructors ← liftTermElabM $ findNonRecursiveConstructors inductiveName
  logInfo s!"nonRecursiveConstructors = {nonRecursiveConstructors}"

  -- Populate a list of sub-generators
  let mut generators := #[]
  for ctor in nonRecursiveConstructors do
    let gen ← liftTermElabM $ getGeneratorForTarget ctor targetIdx
    generators := generators.push gen

  -- Add generator that always fails
  -- TODO: only add this failure generator to the case when `size == 0`
  generators := generators.push (← `((1, $thunkGenFn (fun _ => $failFn))))

  -- Convert the list of generator terms into a Lean list containing all the generators
  let generatorList ← `([$generators,*])

  -- Generate the generator function name
  let genFunName := mkIdent (Name.mkStr1 s!"gen_{inductiveName}")

  -- Create the cases for the pattern-match on the size argument
  let mut caseExprs := #[]
  let zeroCase ← `(Term.matchAltExpr| | $(mkIdent ``Nat.zero) => $backtrackFn $generatorList)
  caseExprs := caseExprs.push zeroCase

  let smallerSize := mkFreshAccessibleIdent localCtx `size'
  let succCase ← `(Term.matchAltExpr| | $(mkIdent ``Nat.succ) $smallerSize => $backtrackFn $generatorList)
  caseExprs := caseExprs.push succCase

  -- Create function argument for the generator size
  let sizeIdent := mkIdent `size
  let sizeParam ← `(Term.letIdBinder| ($sizeIdent : $natIdent))
  let matchExpr ← `(match $sizeIdent:ident with $caseExprs:matchAlt*)

  -- Add parameters for each argument to the inductive relation (except the target)
  let paramInfo ← analyzeInductiveArgs inductiveName args

  -- Top-level params are arguments to the top-level derived generator
  let mut topLevelParams := #[]

  -- Inner params are for the inner `aux_arb` function
  let mut innerParams := #[]
  innerParams := innerParams.push sizeParam

  let mut paramIdents := #[]
  for (paramName, paramType) in paramInfo do
    if paramName != targetVar then
      let paramIdent := mkIdent paramName
      paramIdents := paramIdents.push paramIdent

      let topLevelParam ← `(bracketedBinder| ($paramIdent : $paramType))
      topLevelParams := topLevelParams.push topLevelParam

      let innerParam ← `(Term.letIdBinder| ($paramIdent : $paramType))
      innerParams := innerParams.push innerParam

  -- TODO: when `size == 0`, do `return C` for each arity-0 non-recursive constructor

  -- Produce a fresh name for the `size` argument for the lambda
  -- at the end of the generator function
  let freshSizeIdent := mkFreshAccessibleIdent localCtx `size
  let auxArbIdent := mkFreshAccessibleIdent localCtx `aux_arb
  let generatorType ← `($optionTIdent $genIdent $targetTypeSyntax)

  -- Produce the definition for the generator function
  `(def $genFunName $topLevelParams* : $natIdent → $generatorType :=
      let rec $auxArbIdent:ident $innerParams* : $generatorType :=
        $matchExpr
      fun $freshSizeIdent => $auxArbIdent $freshSizeIdent $paramIdents*)




----------------------------------------------------------------------
-- Command elaborator for producing the Plausible generator
-----------------------------------------------------------------------

syntax (name := derive_generator) "#derive_generator" "(" "fun" "(" ident ":" term ")" "=>" term ")" : command

@[command_elab derive_generator]
def elabDeriveGenerator : CommandElab := fun stx => do
  match stx with
  | `(#derive_generator ( fun ( $var:ident : $typeSyntax:term ) => $body:term )) => do
    -- Parse the body of the lambda for an application of the inductive relation
    let (inductiveName, args) ← parseInductiveApp body
    let targetVar := var.getId

    -- `genFunction` is the syntax for the derived generator function
    let genFunction ← mkGeneratorFunction inductiveName targetVar typeSyntax args

    -- Pretty-print the derived generator
    let genFormat ← liftCoreM (PrettyPrinter.ppCommand genFunction)

    -- Display the code for the derived generator to the user
    -- & prompt the user to accept it in the VS Code side panel
    liftTermElabM $ Tactic.TryThis.addSuggestion stx
      (Format.pretty genFormat) (header := "Try this generator: ")

    logInfo m!"Derived generator:\n{genFormat}"

    elabCommand genFunction

  | _ => throwUnsupportedSyntax

@[command_elab derive_generator]
def elabDeriveGeneratorNew : CommandElab := fun stx => do
  match stx with
  | `(#derive_generator ( fun ( $var:ident : $typeSyntax:term ) => $body:term )) => do

    -- Parse the body of the lambda for an application of the inductive relation
    let (inductiveStx, args) ← deconstructInductiveApplication body
    let targetVar := var.getId

    -- Elaborate the name of the inductive relation and the type
    -- of the value to be generated
    let inductiveExpr ← liftTermElabM $ elabTerm inductiveStx none
    let _targetType ← liftTermElabM $ elabType typeSyntax

    -- Find the index of the argument in the inductive application for the value we wish to generate
    -- (i.e. find `i` s.t. `args[i] == targetVar`)
    let targetIdxOpt := findTargetVarIndex targetVar args
    if let .none := targetIdxOpt then
      throwError "cannot find index of value to be generated"
    let targetIdx := Option.get! targetIdxOpt

    -- Call helper function that produces Thanh's `BacktrackElem` data structure
    let argNameStrings := convertIdentsToStrings args
    let subGeneratorInfos ← liftTermElabM $
      getSubGeneratorInfos inductiveExpr argNameStrings targetIdx


    logInfo m!"hello world!"


  | _ => throwUnsupportedSyntax
