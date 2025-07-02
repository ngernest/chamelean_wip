import Lean
import Plausible.IR.Prelude
import Plausible.New.DeriveGenerator
import Plausible.New.SubCheckers
import Plausible.New.Idents
import Plausible.New.DecOpt

open Lean Elab Command Meta Term Parser
open Idents
open Plausible.IR

/-- Produces an instance of the `DecOpt` typeclass containing the definition for the top-level derived checker.
    The arguments to this function are:
    - a list of `baseCheckers` (each represented as a Lean term), to be invoked when `size == 0`
    - a list of `inductiveCheckers`, to be invoked when `size > 0`
    - the name of the inductive relation (`inductiveStx`)
    - the arguments (`args`) to the inductive relation -/
def mkTopLevelChecker (baseCheckers : TSyntax `term) (inductiveCheckers : TSyntax `term)
  (inductiveStx : TSyntax `term) (args : TSyntaxArray `term) : CommandElabM (TSyntax `command) := do
  -- Fetch the ambient local context, which we need to produce user-accessible fresh names
  let localCtx ← liftTermElabM $ getLCtx

  -- Produce a fresh name for the `size` argument for the lambda
  -- at the end of the checker function, as well as the `aux_dec` inner helper function
  let freshSizeIdent := mkFreshAccessibleIdent localCtx `size
  let freshSize' := mkFreshAccessibleIdent localCtx `size'
  let auxDecIdent := mkFreshAccessibleIdent localCtx `aux_dec
  let checkerType ← `($optionTypeConstructor $boolIdent)

  let inductiveName := inductiveStx.raw.getId

  -- Create the cases for the pattern-match on the size argument
  let mut caseExprs := #[]
  let zeroCase ← `(Term.matchAltExpr| | $(mkIdent ``Nat.zero) => $checkerBacktrackFn $baseCheckers)
  caseExprs := caseExprs.push zeroCase

  let succCase ← `(Term.matchAltExpr| | $(mkIdent ``Nat.succ) $freshSize' => $checkerBacktrackFn $inductiveCheckers)
  caseExprs := caseExprs.push succCase

  -- Create function arguments for the checker's `size` & `initSize` parameters
  -- (former is the generator size, latter is the size argument with which to invoke other auxiliary generators/checkers)
  let initSizeParam ← `(Term.letIdBinder| ($initSizeIdent : $natIdent))
  let sizeParam ← `(Term.letIdBinder| ($sizeIdent : $natIdent))
  let matchExpr ← liftTermElabM $ mkMatchExpr sizeIdent caseExprs

  -- Add parameters for each argument to the inductive relation
  let paramInfo ← analyzeInductiveArgs inductiveName args

  -- Inner params are for the inner `aux_dec` function
  let mut innerParams := #[]
  innerParams := innerParams.push initSizeParam
  innerParams := innerParams.push sizeParam

  -- Outer params are for the top-level lambda function which invokes `aux_arb`
  let mut outerParams := #[]
  for (paramName, paramType) in paramInfo do
    let outerParamIdent := mkIdent paramName
    outerParams := outerParams.push outerParamIdent

    -- Each parameter to the inner `aux_arb` function needs to be a fresh name
    -- (so that if we pattern match on the parameter, we avoid pattern variables from shadowing it)
    let innerParamIdent := mkIdent $ genFreshName (Array.map Prod.fst paramInfo) paramName

    let innerParam ← `(Term.letIdBinder| ($innerParamIdent : $paramType))
    innerParams := innerParams.push innerParam

  -- Produces an instance of the `DecOpt` typeclass containing the definition for the derived generator
  `(instance : $decOptTypeclass ($inductiveStx $args*) where
      $unqualifiedDecOptFn:ident :=
        let rec $auxDecIdent:ident $innerParams* : $checkerType :=
          $matchExpr
        fun $freshSizeIdent => $auxDecIdent $freshSizeIdent $freshSizeIdent $outerParams*)

/-- Produces an instance of the `DecOpt` typeclass for an inductively-defined proposition type
    represented by `indProp` (Note: the main logic for determining the structure of the derived checker.
    is contained in this function.) -/
def mkDecOptInstance (indProp : TSyntax `term) : CommandElabM (TSyntax `command) := do
  -- Parse the for an application of the inductive relation
  let (inductiveName, args) ← deconstructInductiveApplication indProp

  -- Elaborate the name of the inductive relation and the type
  -- of the value to be generated
  let inductiveExpr ← liftTermElabM $ elabTerm inductiveName none

  let argNameStrings := convertIdentsToStrings args

  -- Create an auxiliary `SubGeneratorInfo` structure that
  -- stores the metadata for each derived sub-generator
  let allSubCheckerInfos ← liftTermElabM $ getSubCheckerInfos inductiveExpr argNameStrings

  -- Every generator is an inductive generator
  -- (they can all be invoked in the inductive case of the top-level generator),
  -- but only certain generators qualify as `BaseGenerator`s
  let baseCheckerInfos := Array.filter (fun checker => checker.checkerSort == .BaseChecker) allSubCheckerInfos
  let inductiveCheckerInfos := allSubCheckerInfos

  let baseCheckers ← liftTermElabM $ mkThunkedSubCheckers baseCheckerInfos
  let inductiveCheckers ← liftTermElabM $ mkThunkedSubCheckers inductiveCheckerInfos

  -- Produce an instance of the `DecOpt` typeclass
  mkTopLevelChecker baseCheckers inductiveCheckers inductiveName args


----------------------------------------------------------------------
-- Command elaborator driver
-----------------------------------------------------------------------

syntax (name := derive_checker) "#derive_checker" "(" term ")" : command

/-- Command elaborator that produces the function header for the checker -/
@[command_elab derive_checker]
def elabDeriveChecker : CommandElab := fun stx => do
  match stx with
  | `(#derive_checker ( $indProp:term )) => do

    -- Produce an instance of the `DecOpt` typeclass corresponding to the inductive proposition `indProp`
    let typeclassInstance ← mkDecOptInstance indProp

    -- Pretty-print the derived checker
    let genFormat ← liftCoreM (PrettyPrinter.ppCommand typeclassInstance)

    -- Display the code for the derived checker to the user
    -- & prompt the user to accept it in the VS Code side panel
    liftTermElabM $ Tactic.TryThis.addSuggestion stx
      (Format.pretty genFormat) (header := "Try this checker: ")

    -- Elaborate the typeclass instance and add it to the local context
    elabCommand typeclassInstance

  | _ => throwUnsupportedSyntax
