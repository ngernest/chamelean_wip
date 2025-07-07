import Lean
import Std
import Plausible.IR.Prelude
import Plausible.IR.Constructor
import Plausible.IR.GCCall
import Plausible.New.DeriveGenerator
import Plausible.New.SubEnumerators
import Plausible.New.Idents
import Plausible.New.Utils

open Plausible.IR
open Lean Elab Command Meta Term Parser Std
open Idents

/-- Produces an instance of the `EnumSizedSuchThat` typeclass containing the definition for the top-level derived enumerator.
    The arguments to this function are:
    - a list of `baseEnumerators` (each represented as a Lean term), to be invoked when `size == 0`
    - a list of `inductiveEnumerators`, to be invoked when `size > 0`
    - the name of the inductive relation (`inductiveStx`)
    - the arguments (`args`) to the inductive relation
    - the name and type for the value we wish to enumerate (`targetVar`, `targetTypeSyntax`) -/
def mkTopLevelEnumerator (baseEnumerators : TSyntax `term) (inductiveEnumerators : TSyntax `term) (inductiveStx : TSyntax `term)
  (args : TSyntaxArray `term) (targetVar : Name)
  (targetTypeSyntax : TSyntax `term) : CommandElabM (TSyntax `command) := do
    -- Fetch the ambient local context, which we need to produce user-accessible fresh names
    let localCtx ← liftTermElabM $ getLCtx

    -- Produce a fresh name for the `size` argument for the lambda
    -- at the end of the enumerator function, as well as the `aux_enum` inner helper function
    let freshSizeIdent := mkFreshAccessibleIdent localCtx `size
    let freshSize' := mkFreshAccessibleIdent localCtx `size'
    let auxEnumIdent := mkFreshAccessibleIdent localCtx `aux_enum
    let enumeratorType ← `($optionTTypeConstructor $enumTypeConstructor $targetTypeSyntax)

    let inductiveName := inductiveStx.raw.getId

    -- Create the cases for the pattern-match on the size argument
    let mut caseExprs := #[]
    let zeroCase ← `(Term.matchAltExpr| | $(mkIdent ``Nat.zero) => $enumerateFn $baseEnumerators)
    caseExprs := caseExprs.push zeroCase

    let succCase ← `(Term.matchAltExpr| | $(mkIdent ``Nat.succ) $freshSize' => $enumerateFn $inductiveEnumerators)
    caseExprs := caseExprs.push succCase

    -- Create function arguments for the enumerator's `size` & `initSize` parameters
    -- (former is the enumerator size, latter is the size argument with which to invoke other auxiliary enumerators/checkers)
    let initSizeParam ← `(Term.letIdBinder| ($initSizeIdent : $natIdent))
    let sizeParam ← `(Term.letIdBinder| ($sizeIdent : $natIdent))
    let matchExpr ← liftTermElabM $ mkMatchExpr sizeIdent caseExprs

    -- Add parameters for each argument to the inductive relation
    -- (except the target variable, which we'll filter out later)
    let paramInfo ← analyzeInductiveArgs inductiveName args

    -- Inner params are for the inner `aux_enum` function
    let mut innerParams := #[]
    innerParams := innerParams.push initSizeParam
    innerParams := innerParams.push sizeParam

    -- Outer params are for the top-level lambda function which invokes `aux_enum`
    let mut outerParams := #[]
    for (paramName, paramType) in paramInfo do
      -- Only add a function parameter is the argument to the inductive relation is not the target variable
      -- (We skip the target variable since that's the value we wish to generate)
      if paramName != targetVar then
        let outerParamIdent := mkIdent paramName
        outerParams := outerParams.push outerParamIdent

        -- Each parameter to the inner `aux_arb` function needs to be a fresh name
        -- (so that if we pattern match on the parameter, we avoid pattern variables from shadowing it)
        let innerParamIdent := mkIdent $ genFreshName (Array.map Prod.fst paramInfo) paramName

        let innerParam ← `(Term.letIdBinder| ($innerParamIdent : $paramType))
        innerParams := innerParams.push innerParam

    -- Produces an instance of the `EnumSizedSuchThat` typeclass containing the definition for the derived enumerator
    `(instance : $enumSizedSuchThatTypeclass $targetTypeSyntax (fun $(mkIdent targetVar) => $inductiveStx $args*) where
        $unqualifiedEnumSizedSTFn:ident :=
          let rec $auxEnumIdent:ident $innerParams* : $enumeratorType :=
            $matchExpr
          fun $freshSizeIdent => $auxEnumIdent $freshSizeIdent $freshSizeIdent $outerParams*)


syntax (name := derive_enumerator) "#derive_enumerator" "(" "fun" "(" ident ":" term ")" "=>" term ")" : command

@[command_elab derive_enumerator]
def elabDeriveEnumerator : CommandElab := fun stx => do
  match stx with
  | `(#derive_enumerator ( fun ( $var:ident : $targetTypeSyntax:term ) => $body:term )) => do

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
    let allSubGeneratorInfos ← liftTermElabM $ getSubGeneratorInfos inductiveExpr argNameStrings targetIdx .Enumerator

    -- Every generator is an inductive generator
    -- (they can all be invoked in the inductive case of the top-level generator),
    -- but only certain generators qualify as `BaseGenerator`s
    let baseGenInfo := Array.filter (fun gen => gen.generatorSort == .BaseGenerator) allSubGeneratorInfos
    let inductiveGenInfo := allSubGeneratorInfos

    let baseEnumerators ← liftTermElabM $ mkSubEnumeratorList baseGenInfo .BaseGenerator
    let inductiveEnumerators ← liftTermElabM $ mkSubEnumeratorList inductiveGenInfo .InductiveGenerator

    let typeclassInstance ← mkTopLevelEnumerator baseEnumerators inductiveEnumerators inductiveName args targetVar targetTypeSyntax

    -- Pretty-print the derived generator
    let genFormat ← liftCoreM (PrettyPrinter.ppCommand typeclassInstance)

    -- Display the code for the derived generator to the user
    -- & prompt the user to accept it in the VS Code side panel
    liftTermElabM $ Tactic.TryThis.addSuggestion stx
      (Format.pretty genFormat) (header := "Try this generator: ")

    -- Elaborate the typeclass instance and add it to the local context
    elabCommand typeclassInstance

  | _ => throwUnsupportedSyntax
