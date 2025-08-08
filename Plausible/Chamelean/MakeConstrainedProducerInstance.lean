import Lean
import Std
import Plausible.Gen
import Plausible.Chamelean.TSyntaxCombinators
import Plausible.Chamelean.OptionTGen
import Plausible.Chamelean.Idents
import Plausible.Chamelean.Utils
import Plausible.Chamelean.Schedules


open Lean Elab Command Meta Term Parser Std
open Idents

/-- Extracts the name of the induction relation and its arguments -/
def parseInductiveApp (body : Term) : CommandElabM (TSyntax `ident × TSyntaxArray `ident) := do
  match body with
  | `($lhs:ident = $rhs:ident) =>
    return (Lean.mkIdent ``Eq, #[lhs, rhs])
  | `($indRel:ident $args:ident*) =>
    return (indRel, args)
  | `($indRel:ident) =>
    return (indRel, #[])
  | _ => throwErrorAt body m!"{body} is not a valid application of an inductive relation, all arguments should be either literals or variables"

/-- Finds the index of the argument in the inductive application for the value we wish to generate
    (i.e. finds `i` s.t. `args[i] == targetVar`) -/
def findTargetVarIndex (targetVar : Name) (args : TSyntaxArray `term) : Option Nat :=
  Array.findIdx? (fun arg => arg.getId == targetVar) (TSyntaxArray.raw args)

/-- Produces an instance of the `ArbitrarySizedSuchThat` / `EnumSizedSuchThat` typeclass containing the definition for a constrained generator.
    The arguments to this function are:
    - a list of `baseGenerators` (each represented as a Lean term), to be invoked when `size == 0`
    - a list of `inductiveGenerators`, to be invoked when `size > 0`
    - the name of the inductive relation (`inductiveStx`)
    - the names and types to the inductive relation (`argNameTypes`)
    - the name and type for the value we wish to generate (`targetVar`, `targetTypeSyntax`)
    - the `producerType`, which determines what typeclass is to be produced
      + If `producerType = .Generator`, an `ArbitrarySizedSuchThat` instance is produced
      + If `producerType = .Enumerator`, an `EnumSizedSuchThat` instance is produced
    - The `LocalContext` associated with the top-level inductive relation (`topLevelLocalCtx`) -/
def mkConstrainedProducerTypeClassInstance
  (baseGenerators : TSyntax `term)
  (inductiveGenerators : TSyntax `term)
  (inductiveStx : TSyntax `term)
  (argNameTypes : Array (Name × Expr))
  (targetVar : Name)
  (targetTypeSyntax : TSyntax `term)
  (producerSort : ProducerSort)
  (topLevelLocalCtx : LocalContext) : CommandElabM (TSyntax `command) := do
    -- Produce a fresh name for the `size` argument for the lambda
    -- at the end of the generator function, as well as the `aux_arb` inner helper function
    let freshSizeIdent := mkFreshAccessibleIdent topLevelLocalCtx `size
    let freshSize' := mkFreshAccessibleIdent topLevelLocalCtx `size'

    -- The (backtracking) combinator to be invoked
    -- (`OptionTGen.backtrack` for generators, `EnumeratorCombinators.enumerate` for enumerators)
    let combinatorFn :=
      match producerSort with
      | .Generator => OptionTBacktrackFn
      | .Enumerator => enumerateFn

    -- Create the cases for the pattern-match on the size argument
    let mut caseExprs := #[]
    let zeroCase ← `(Term.matchAltExpr| | $(mkIdent ``Nat.zero) => $combinatorFn $baseGenerators)
    caseExprs := caseExprs.push zeroCase

    let succCase ← `(Term.matchAltExpr| | $(mkIdent ``Nat.succ) $freshSize' => $combinatorFn $inductiveGenerators)
    caseExprs := caseExprs.push succCase

    -- Create function arguments for the producer's `size` & `initSize` parameters
    -- (former is the generator size, latter is the size argument with which to invoke other auxiliary producers/checkers)
    let initSizeParam ← `(Term.letIdBinder| ($initSizeIdent : $natIdent))
    let sizeParam ← `(Term.letIdBinder| ($sizeIdent : $natIdent))
    let matchExpr ← liftTermElabM $ mkMatchExpr sizeIdent caseExprs

    -- Inner params are for the inner `aux_arb` / `aux_enum` function
    let mut innerParams := #[]
    innerParams := innerParams.push initSizeParam
    innerParams := innerParams.push sizeParam

    -- Outer params are for the top-level lambda function which invokes `aux_arb` / `aux_enum`
    let mut outerParams := #[]
    for (paramName, paramType) in argNameTypes do
      -- Only add a function parameter is the argument to the inductive relation is not the target variable
      -- (We skip the target variable since that's the value we wish to generate)
      if paramName != targetVar then
        let outerParamIdent := mkIdent paramName
        outerParams := outerParams.push outerParamIdent

        -- Inner parameters are for the inner `aux_arb` / `aux_enum` function
        let innerParamType ← liftTermElabM $ PrettyPrinter.delab paramType
        let innerParam ← `(Term.letIdBinder| ($(mkIdent paramName) : $innerParamType))
        innerParams := innerParams.push innerParam

    -- Figure out which typeclass should be derived
    -- (`ArbitrarySizedSuchThat` for generators, `EnumSizedSuchThat` for enumerators)
    let producerTypeClass :=
      match producerSort with
      | .Generator => arbitrarySizedSuchThatTypeclass
      | .Enumerator => enumSizedSuchThatTypeclass

    -- Similarly, figure out the name of the function corresponding to the typeclass above
    let producerTypeClassFunction :=
      match producerSort with
      | .Generator => unqualifiedArbitrarySizedSTFn
      | .Enumerator => unqualifiedEnumSizedSTFn

    -- Generators use `aux_arb` as the inner function, enumerators use `aux_enum`
    let innerFunctionIdent :=
      match producerSort with
      | .Generator => mkFreshAccessibleIdent topLevelLocalCtx `aux_arb
      | .Enumerator => mkFreshAccessibleIdent topLevelLocalCtx `aux_enum

    -- Determine the appropriate type constructor to use as the producer's type
    -- (either `Gen` or `Enumerator`)
    let producerTypeConstructor :=
      match producerSort with
      | .Generator => genTypeConstructor
      | .Enumerator => enumTypeConstructor

    -- Determine the appropriate type of the final producer
    -- (either `OptionT Plausible.Gen α` or `OptionT Enum α`)
    let optionTProducerType ← `($optionTTypeConstructor $producerTypeConstructor $targetTypeSyntax)

    -- Extract all the args to the inductive relation
    let args := (fun (arg, _) => mkIdent arg) <$> argNameTypes

    -- Produce an instance of the appropriate typeclass containing the definition for the derived producer
    `(instance : $producerTypeClass $targetTypeSyntax (fun $(mkIdent targetVar) => $inductiveStx $args*) where
        $producerTypeClassFunction:ident :=
          let rec $innerFunctionIdent:ident $innerParams* : $optionTProducerType :=
            $matchExpr
          fun $freshSizeIdent => $innerFunctionIdent $freshSizeIdent $freshSizeIdent $outerParams*)
