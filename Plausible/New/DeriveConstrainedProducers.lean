import Lean
import Std
import Plausible.IR.Prelude
import Plausible.IR.Constructor
import Plausible.IR.Action
import Plausible.Gen
import Plausible.New.OptionTGen
import Plausible.New.SubGenerators
import Plausible.New.SubEnumerators
import Plausible.New.Idents
import Plausible.New.Utils

open Plausible.IR
open Lean Elab Command Meta Term Parser Std
open Idents

/-- Extracts the name of the induction relation and its arguments -/
def parseInductiveApp (body : Term) : CommandElabM (Name × TSyntaxArray `ident) := do
  match body with
  | `($indRel:ident $args:ident*) => do
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


/-- Produces an instance of the `ArbitrarySizedSuchThat` / `EnumSizedSuchThat` typeclass containing the definition for the top-level derived generator.
    The arguments to this function are:
    - a list of `baseGenerators` (each represented as a Lean term), to be invoked when `size == 0`
    - a list of `inductiveGenerators`, to be invoked when `size > 0`
    - the name of the inductive relation (`inductiveStx`)
    - the arguments (`args`) to the inductive relation
    - the name and type for the value we wish to generate (`targetVar`, `targetTypeSyntax`)
    - the `producerType`, which determines what typeclass is to be produced
      + If `producerType = .Generator`, an `ArbitrarySizedSuchThat` instance is produced
      + If `producerType = .Enumerator`, an `EnumSizedSuchThat` instance is produced -/
def mkProducerTypeClassInstance (baseGenerators : TSyntax `term) (inductiveGenerators : TSyntax `term) (inductiveStx : TSyntax `term)
  (args : TSyntaxArray `term) (targetVar : Name)
  (targetTypeSyntax : TSyntax `term) (producerType : ProducerType)
  (topLevelLocalCtx : LocalContext) (nameMap : HashMap Name Name) : CommandElabM (TSyntax `command) := do
    -- Produce a fresh name for the `size` argument for the lambda
    -- at the end of the generator function, as well as the `aux_arb` inner helper function
    let freshSizeIdent := mkFreshAccessibleIdent topLevelLocalCtx `size
    let freshSize' := mkFreshAccessibleIdent topLevelLocalCtx `size'

    let inductiveName := inductiveStx.raw.getId

    -- The (backtracking) combinator to be invoked
    -- (`OptionTGen.backtrack` for generators, `EnumeratorCombinators.enumerate` for enumerators)
    let combinatorFn :=
      match producerType with
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

    -- Add parameters for each argument to the inductive relation
    -- (except the target variable, which we'll filter out later)
    let paramInfo ← analyzeInductiveArgs inductiveName args

    -- Inner params are for the inner `aux_arb` / `aux_enum` function
    let mut innerParams := #[]
    innerParams := innerParams.push initSizeParam
    innerParams := innerParams.push sizeParam

    -- Outer params are for the top-level lambda function which invokes `aux_arb` / `aux_enum`
    let mut outerParams := #[]
    for (paramName, paramType) in paramInfo do
      -- Only add a function parameter is the argument to the inductive relation is not the target variable
      -- (We skip the target variable since that's the value we wish to generate)
      if paramName != targetVar then
        let outerParamIdent := mkIdent paramName
        outerParams := outerParams.push outerParamIdent

        -- Each parameter to the inner `aux_arb` function needs to be a fresh name
        -- (so that if we pattern match on the parameter, we avoid pattern variables from shadowing it)
        -- We obtain this fresh name by looking up in the `nameMap`
        let innerParamIdent := lookupFreshenedNameInNameMap nameMap (Array.map Prod.fst paramInfo) paramName

        let innerParam ← `(Term.letIdBinder| ($innerParamIdent : $paramType))
        innerParams := innerParams.push innerParam

    -- Figure out which typeclass should be derived
    -- (`ArbitrarySizedSuchThat` for generators, `EnumSizedSuchThat` for enumerators)
    let producerTypeClass :=
      match producerType with
      | .Generator => arbitrarySizedSuchThatTypeclass
      | .Enumerator => enumSizedSuchThatTypeclass

    -- Similarly, figure out the name of the function corresponding to the typeclass above
    let producerTypeClassFunction :=
      match producerType with
      | .Generator => unqualifiedArbitrarySizedSTFn
      | .Enumerator => unqualifiedEnumSizedSTFn

    -- Generators use `aux_arb` as the inner function, enumerators use `aux_enum`
    let innerFunctionIdent :=
      match producerType with
      | .Generator => mkFreshAccessibleIdent topLevelLocalCtx `aux_arb
      | .Enumerator => mkFreshAccessibleIdent topLevelLocalCtx `aux_enum

    -- Determine the appropriate type constructor to use as the producer's type
    -- (either `Gen` or `Enumerator`)
    let producerTypeConstructor :=
      match producerType with
      | .Generator => genTypeConstructor
      | .Enumerator => enumTypeConstructor

    -- Determine the appropriate type of the final producer
    -- (either `OptionT Plausible.Gen α` or `OptionT Enum α`)
    let optionTProducerType ← `($optionTTypeConstructor $producerTypeConstructor $targetTypeSyntax)

    -- Produce an instance of the appropriate typeclass containing the definition for the derived producer
    `(instance : $producerTypeClass $targetTypeSyntax (fun $(mkIdent targetVar) => $inductiveStx $args*) where
        $producerTypeClassFunction:ident :=
          let rec $innerFunctionIdent:ident $innerParams* : $optionTProducerType :=
            $matchExpr
          fun $freshSizeIdent => $innerFunctionIdent $freshSizeIdent $freshSizeIdent $outerParams*)
