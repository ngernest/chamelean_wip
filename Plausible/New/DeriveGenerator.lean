import Lean
import Std
import Plausible.IR.Prelude
import Plausible.IR.Constructor
import Plausible.IR.GCCall
import Plausible.Gen
import Plausible.New.OptionTGen
import Plausible.New.SubGenerators
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

----------------------------------------------------------------------
-- Command elaborator for producing the Plausible generator
-----------------------------------------------------------------------

syntax (name := derive_generator) "#derive_generator" "(" "fun" "(" ident ":" term ")" "=>" term ")" : command

/-- Creates the top-level derived generator based on:
    - a list of `baseGenerators` (each represented as a Lean term), to be invoked when `size == 0`
    - a list of `inductiveGenerators`, to be invoked when `size > 0`
    - the name of the inductive relation (`inductiveStx`)
    - the arguments (`args`) to the inductive relation
    - the name and type for the value we wish to generate (`targetVar`, `targetTypeSyntax`) -/
def mkTopLevelGenerator (baseGenerators : TSyntax `term) (inductiveGenerators : TSyntax `term) (inductiveStx : TSyntax `term)
  (args : TSyntaxArray `term) (targetVar : Name)
  (targetTypeSyntax : TSyntax `term) : CommandElabM (TSyntax `command) := do
    -- Fetch the ambient local context, which we need to produce user-accessible fresh names
    let localCtx ← liftTermElabM $ getLCtx

    let inductiveName := inductiveStx.raw.getId

    -- Create the cases for the pattern-match on the size argument
    let mut caseExprs := #[]
    let zeroCase ← `(Term.matchAltExpr| | $(mkIdent ``Nat.zero) => $backtrackFn $baseGenerators)
    caseExprs := caseExprs.push zeroCase

    let succCase ← `(Term.matchAltExpr| | $(mkIdent ``Nat.succ) $(mkIdent `size') => $backtrackFn $inductiveGenerators)
    caseExprs := caseExprs.push succCase

    -- Create function argument for the generator size
    let initSizeParam ← `(Term.letIdBinder| ($initSizeIdent : $natIdent))
    let sizeParam ← `(Term.letIdBinder| ($sizeIdent : $natIdent))
    let matchExpr ← liftTermElabM $ mkMatchExpr sizeIdent caseExprs

    -- Add parameters for each argument to the inductive relation (except the target)
    let paramInfo ← analyzeInductiveArgs inductiveName args

    -- Top-level params are arguments to the top-level derived generator
    let mut topLevelParams := #[]

    -- Inner params are for the inner `aux_arb` function
    let mut innerParams := #[]
    innerParams := innerParams.push initSizeParam
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

    -- Produce a fresh name for the `size` argument for the lambda
    -- at the end of the generator function
    let freshSizeIdent := mkFreshAccessibleIdent localCtx `size
    let auxArbIdent := mkFreshAccessibleIdent localCtx `aux_arb
    let generatorType ← `($optionTIdent $genIdent $targetTypeSyntax)

    -- Produces an instance of `GenSizedSuchThat` typeclass containing the definition for the derived generator
    `(instance : $genSizedSuchThatTypeclass:ident $targetTypeSyntax (fun $(mkIdent targetVar) => $inductiveStx $args*) where
        $genSizedSTIdent:ident :=
          let rec $auxArbIdent:ident $innerParams* : $generatorType :=
            $matchExpr
          fun $freshSizeIdent => $auxArbIdent $freshSizeIdent $freshSizeIdent $paramIdents*)


@[command_elab derive_generator]
def elabDeriveGenerator : CommandElab := fun stx => do
  match stx with
  | `(#derive_generator ( fun ( $var:ident : $targetTypeSyntax:term ) => $body:term )) => do

    -- Parse the body of the lambda for an application of the inductive relation
    let (inductiveName, args) ← deconstructInductiveApplication body
    let targetVar := var.getId

    -- Elaborate the name of the inductive relation and the type
    -- of the value to be generated
    let inductiveExpr ← liftTermElabM $ elabTerm inductiveName none

    -- Find the index of the argument in the inductive application for the value we wish to generate
    -- (i.e. find `i` s.t. `args[i] == targetVar`)
    let targetIdxOpt := findTargetVarIndex targetVar args
    if let .none := targetIdxOpt then
      throwError "cannot find index of value to be generated"
    let targetIdx := Option.get! targetIdxOpt

    let argNameStrings := convertIdentsToStrings args

    -- Create an auxiliary `SubGeneratorInfo` structure that
    -- stores the metadata for each derived sub-generator
    let allSubGeneratorInfos ← liftTermElabM $ getSubGeneratorInfos inductiveExpr argNameStrings targetIdx

    -- Every generator is an inductive generator
    -- (they can all be invoked in the inductive case of the top-level generator),
    -- but only certain generators qualify as `BaseGenerator`s
    let baseGenInfo := Array.filter (fun gen => gen.generatorSort == .BaseGenerator) allSubGeneratorInfos
    let inductiveGenInfo := allSubGeneratorInfos

    let baseGenerators ← liftTermElabM $ mkWeightedThunkedSubGenerators baseGenInfo .BaseGenerator
    let inductiveGenerators ← liftTermElabM $ mkWeightedThunkedSubGenerators inductiveGenInfo .InductiveGenerator

    let generatorDefinition ← mkTopLevelGenerator baseGenerators inductiveGenerators inductiveName args targetVar targetTypeSyntax

    -- Pretty-print the derived generator
    let genFormat ← liftCoreM (PrettyPrinter.ppCommand generatorDefinition)

    -- Display the code for the derived generator to the user
    -- & prompt the user to accept it in the VS Code side panel
    liftTermElabM $ Tactic.TryThis.addSuggestion stx
      (Format.pretty genFormat) (header := "Try this generator: ")

    elabCommand generatorDefinition

  | _ => throwUnsupportedSyntax
