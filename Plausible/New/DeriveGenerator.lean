import Lean
import Plausible.New.GenOption
import Plausible.IR.Prelude
import Plausible.Gen

open Plausible.IR
open Lean Elab Command Meta Term Parser

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

  -- TODO: figure out what are the first two components of the
  -- triple returned by `decompose_type`
  let (_, _, type_exprs_in_arrow_type) ← decompose_type ctorType
  match splitLast? type_exprs_in_arrow_type with
  | some (hypotheses, _conclusion) =>
    for hyp in hypotheses do
      if hyp.getAppFn.constName == inductiveName then
        return true
    return false
  | none => throwError "constructors with non-arrow types are not-considered to be recursive"

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
  let constructorNames := inductInfo.ctors

  -- Print the arity of each constructor
  for ctorName in constructorNames do
    let ctorInfo ← getConstInfoCtor ctorName
    IO.println s!"ctor {ctorName} has arity {ctorInfo.numFields}"

  -- Find the names of all non-recursive constructors
  let nonRecursiveConstructors ← liftTermElabM $ findNonRecursiveConstructors inductiveName
  logInfo s!"non-recursive constructors: {nonRecursiveConstructors.toList}"


  -- Generate the generator function name
  let genFunName := mkIdent (Name.mkStr1 s!"gen_{inductiveName}")

  -- Create function argument for the generator size
  let mut params := #[]
  let sizeParam ← `(bracketedBinder| (size : Nat))
  params := params.push sizeParam

  -- Add parameters for each argument to the inductive relation (except the target)
  let paramInfo ← analyzeInductiveArgs inductiveName args
  for (paramName, paramType) in paramInfo do
    if paramName != targetVar then
      let paramIdent := mkIdent paramName
      let param ← `(bracketedBinder| ($paramIdent : $paramType))
      params := params.push param

  -- TODO: when `size == 0`, do `return C` for each arity-0 non-recursive constructor

  -- Produce the definition for the generator function
  -- TODO: switch to `backtrack` combinator instead of `Gen.oneOf`
  -- once the array of sub-generators has been populated
  `(def $genFunName $params* : Plausible.Gen (Option $targetType) :=
      match size with
      | .zero => Plausible.Gen.oneOf #[return none]
      | .succ size' => Plausible.Gen.oneOf #[return none])

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
    logInfo m!"Generated generator function:\n{genFormat}"

    elabCommand genFunction

  | _ => throwUnsupportedSyntax
