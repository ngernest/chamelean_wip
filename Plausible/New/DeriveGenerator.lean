import Lean
import Plausible.New.GenOption
import Plausible.IR.Prelude
import Plausible.Gen
import Plausible.New.OptionTGen

open Plausible.IR
open Lean Elab Command Meta Term Parser


-- Create an ident for each function in the auxiliary `OptionTGen` library
def thunkGenFn : Ident :=
  mkIdent $ Name.mkStr2 "OptionTGen" "thunkGen"
def backtrackFn : Ident :=
  mkIdent $ Name.mkStr2 "OptionTGen" "backtrack"

def natIdent : Ident := mkIdent ``Nat
def optionTIdent : Ident := mkIdent ``OptionT
def genIdent : Ident := mkIdent ``Plausible.Gen

/-- Extracts the name of the induction relation and its arguments -/
def parseInductiveApp (body : Term) : CommandElabM (Name × TSyntaxArray `term) := do
  match body with
  | `($indRel:ident $args:term*) => do
    return (indRel.getId, args)
  | `($indRel:ident) => do
    return (indRel.getId, #[])
  | _ => throwErrorAt body "Expected inductive type application"

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
  let ctorInfo ← getConstInfo ctorName
  let ctorType := ctorInfo.type

  let (_, _, type_exprs_in_arrow_type) ← decomposeType ctorType
  match splitLast? type_exprs_in_arrow_type with
  | some (_hypotheses, conclusion) =>
    -- TOOD: handle the hypotheses for the constructor

    -- TODO: handle other arguments in the conclusion (we need to generate them as well)
    -- (see how free variables are generated in `GenCheckCalls_for_producer`)

    -- Find the argument (an `Expr`) corresponding to the value we wish to generate,
    -- then delaborate it to a `Term`
    let argToGenExpr := conclusion.getAppArgs[targetIdx]!
    let argToGenTerm ← PrettyPrinter.delab argToGenExpr
    `((1, $thunkGenFn (fun _ => pure $argToGenTerm)))
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

/-- Produces the actual generator function.
    - `inductiveName` is the name of the inductive relation
    - `targetVar`, `targetType`: the variable name and type of the value to be generated
    - `args`: the other arguments to the inductive relation -/
def mkGeneratorFunction (inductiveName : Name) (targetVar : Name) (targetType : TSyntax `term)
  (args : TSyntaxArray `term) : CommandElabM (TSyntax `command) := do
  -- Extract the names of the constructors for the inductive
  let inductInfo ← getConstInfoInduct inductiveName
  let _constructorNames := inductInfo.ctors

  -- Find the index of the argument in the inductive application for the value we wish to generate
  -- (i.e. find `i` s.t. `args[i] == targetVar`)
  let targetIdxOpt := Array.findIdx? (fun arg => arg.getId == targetVar) (TSyntaxArray.raw args)
  if let .none := targetIdxOpt then
    throwError "cannot find index of value to be generated"
  let targetIdx := Option.get! targetIdxOpt
  logInfo s!"varIdx = {targetIdx}"

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
  generators := generators.push (← `((1, $thunkGenFn (fun _ => OptionT.fail))))

  -- Convert the list of generator terms into a Lean list
  -- containing all the generators
  let generatorList ← `([$generators,*])

  -- Generate the generator function name
  let genFunName := mkIdent (Name.mkStr1 s!"gen_{inductiveName}")

  -- Create function argument for the generator size
  let sizeIdent := mkIdent `size
  let sizeParam ← `(Term.letIdBinder| ($sizeIdent : $natIdent))

  let mut caseExprs := #[]
  let zeroCase ← `(Term.matchAltExpr| | zero => $backtrackFn $generatorList)
  let succCase ← `(Term.matchAltExpr| | .succ size' => $backtrackFn $generatorList)
  caseExprs := caseExprs.push zeroCase
  caseExprs := caseExprs.push succCase
  let matchExpr ← `(match $sizeIdent:ident with $caseExprs:matchAlt*)

  -- Add parameters for each argument to the inductive relation (except the target)
  let paramInfo ← analyzeInductiveArgs inductiveName args
  let mut topLevelParams := #[]
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
  let freshSizeIdent ← liftTermElabM (Lean.mkIdent <$> mkFreshUserName `size)
  let freshSizeArgBinder ← `(Term.funBinder| $freshSizeIdent)

  let auxArb := Name.mkStr1 "aux_arb"
  let auxArbIdent := mkIdent auxArb
  let generatorType ← `($optionTIdent $genIdent $targetType)

  -- Produce the definition for the generator function
  `(def $genFunName $topLevelParams* : $natIdent → $generatorType :=
      let rec $auxArbIdent:ident $innerParams* : $generatorType :=
        $matchExpr
      fun $freshSizeArgBinder => $auxArbIdent $freshSizeIdent $paramIdents*)

----------------------------------------------------------------------
-- Command elaborator for producing the Plausible generator
-----------------------------------------------------------------------

syntax (name := derive_generator) "#derive_generator" "(" "fun" "(" ident ":" term ")" "=>" term ")" : command

@[command_elab derive_generator]
def elabDeriveGenerator : CommandElab := fun stx => do
  match stx with
  | `(#derive_generator ( fun ( $var:ident : $targetType:term ) => $body:term )) => do
    -- Parse the body of the lambda for an application of the inductive relation
    let (inductiveName, args) ← parseInductiveApp body
    let targetVar := var.getId

    -- `genFunction` is the syntax for the derived generator function
    let genFunction ← mkGeneratorFunction inductiveName targetVar targetType args

    -- Pretty-print the derived generator
    let genFormat ← liftCoreM (PrettyPrinter.ppCommand genFunction)
    let prettyGen := Format.pretty genFormat

    -- Display the code for the derived generator to the user
    -- & prompt the user to accept it in the VS Code side panel
    liftTermElabM $ Tactic.TryThis.addSuggestion stx
      prettyGen (header := "Derived generator: ")

    logInfo s!"Derived generator:\n{prettyGen}"

    elabCommand genFunction

  | _ => throwUnsupportedSyntax
