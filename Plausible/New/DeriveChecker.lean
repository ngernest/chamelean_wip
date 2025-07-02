import Lean
import Plausible.IR.Prelude
import Plausible.New.DeriveGenerator
import Plausible.New.SubCheckers
import Plausible.New.Idents

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
  `(instance : $decOptTypeclass (inductiveStx $args*) where
      $unqualifiedDecOptFn:ident :=
        let rec $auxDecIdent:ident $innerParams* : $checkerType :=
          $matchExpr
        fun $freshSizeIdent => $auxDecIdent $freshSizeIdent $freshSizeIdent $outerParams*)


----------------------------------------------------------------------
-- Command elaborator driver
-----------------------------------------------------------------------

syntax (name := derive_checker) "#derive_checker" "(" term ")" : command

/-- Command elaborator that produces the function header for the checker -/
@[command_elab derive_checker]
def elabDeriveChecker : CommandElab := fun stx => do
  match stx with
  | `(#derive_checker ( $body:term )) => do
    -- Parse the body of the lambda for an application of the inductive relation
    let (inductiveName, args) ← deconstructInductiveApplication body

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

    let baseCheckers ← Array.mapM (fun chk => liftTermElabM $ mkSubChecker chk) baseCheckerInfos
    let inductiveCheckers ← Array.mapM (fun chk => liftTermElabM $ mkSubChecker chk) inductiveCheckerInfos

  | _ => throwUnsupportedSyntax

-- TODO: see if we can implement a deriving handler to support
-- `deriving instance DecOpt for (bst lo hi t)` syntax

#derive_checker (bst lo hi t)
-- #derive_checker (balanced n t)
-- #derive_checker (lookup Γ x τ)
-- #derive_checker (typing Γ e τ)

/-

let rec aux_arb (initSize : Nat) (size : Nat) (lo_0 : Nat) (hi_0 : Nat) (t_0 : Tree) : Option Bool :=
  match size with
  | .zero =>
    DecOpt.checkerBacktrack [
      fun _ =>
        match t_0 with
        | .Leaf => some true
        | .Node _ _ _ => some false,
      fun _ => none
    ]
  | .succ size' =>
    DecOpt.checkerBacktrack [
      fun _ =>
        match t_0 with
        | .Leaf => some true
        | .Node _ _ _ => some false,
      fun _ =>
        match t_0 with
        | .Leaf => some false
        | .Node x l r =>
          DecOpt.andOptList [
            DecOpt.decOpt (lo_0 < x && x < hi_0) initSize,
            aux_arb initSize size' lo_0 x l,
            aux_arb initSize size' x hi_0 r
          ]
    ]

-/
