import Lean
import Plausible.IR.Examples
import Plausible.IR.Extractor
import Plausible.IR.Prelude

import Plausible.IR.Action
import Plausible.New.Utils
import Plausible.New.Debug
open List Nat Array String Std
open Lean Elab Command Meta Term

namespace Plausible.IR

/-- Datatype representing an ordered collection of `Action`s, sorted according to
    which constructor was used to create each `Action`
    - Note: `GroupedActions` was previously called `GenCheckCall_group` -/
structure GroupedActions where
  gen_list: Array Action

  /-- `iflet_list` is the list of `if let ...` expressions -/
  iflet_list : Array Action

  /-- An array of `Action`s where all of them are created using the `checkInductive` constructor -/
  checkInductiveActions: Array Action

  /-- An array of `Action`s where all of them are created using the `checkNonInductive` constructor -/
  checkNonInductiveActions: Array Action

  /-- `ret_list` is the `Action`s which are all of the form `return e` -/
  ret_list : Array Action

  /-- A collection of equations (each represented as an `Expr`) relating variables to each other
      (e.g. `t = t1`) -/
  variableEqs : Array Expr

  deriving Repr

/-- Determines whether a generator is to be invoked during the base case when `size == 0` (`BaseGenerator`),
    or if it is inductively-defined (`InductiveGenerator`) and to be invoked when `size > 0` -/
inductive GeneratorSort where
  | BaseGenerator
  | InductiveGenerator
  deriving Repr, BEq

/-- Determines whether a checker is to be invoked during the base case when `size == 0` (`BaseChecker`),
    or if it is inductively-defined (`InductiveChecker`) and to be invoked when `size > 0`
    - We define `CheckerSort` as a separate datatype to avoid confusing it with `GeneratorSort` -/
inductive CheckerSort where
  | BaseChecker
  | InductiveChecker
  deriving Repr, BEq

/-- Determines whether a producer is a `Generator` or an `Enumerator` -/
inductive ProducerType where
  | Generator
  | Enumerator
  deriving Repr, BEq


/-- Datatype containing metadata needed to derive a handler
    (handlers are a generalization of sub-generators/sub-checkers)
    - See the `SubGeneratorInfo` & `SubCheckerInfo` types, which extend this type
      with extra fields -/
structure HandlerInfo where
  /-- Argument names for each sub-generator / sub-checker -/
  inputs : Array String

  /-- Arguments that should be matched in the outer-most
      pattern match in the backtrack element
      (note that the input is the scrutinee for the match expression)
      - Invariant: `matchCases.length == inputsToMatch.length` -/
  inputsToMatch : Array String

  /-- Cases (LHS) of the pattern match mentioned above
    - The RHS of each case should be the derived generator
    - Invariant: `matchCases.length == inputsToMatch.length` -/
  matchCases : Array Expr

  /-- `groupedActions` is used to create the RHS of the first case
      in the pattern match -/
  groupedActions : GroupedActions

  /-- `LocalContext` associated with all the `FVarId`s -/
  localCtx : LocalContext

  /-- A list of equalities (represented as `Expr`s) that must hold between variables
      (used when rewriting variables in patterns) -/
  variableEqs : Array Expr

  /-- A `HashMap` mapping argument names to freshened versions of the same name
      (the other `LocalContext` field in `HandlerInfo` only stores the freshened version) -/
  nameMap : HashMap Name Name

  deriving Repr

/-- Datatype containing metadata needed to derive a sub-generator
    that is invoked from the main generator function
    - Note: this type was previously called `BacktrackElem` -/
structure SubGeneratorInfo extends HandlerInfo where
  /-- `generatorSort` determines if the sub-generator is to be invoked
       when `size == 0` (i.e. it is a `BaseGenerator`), or if it is to be invoked
       when `size > 0` (i.e. the sub-generator is inductively defined and makes
       recursive calls) -/
  generatorSort : GeneratorSort

  /-- Determines whether the producer is a generator or an enumerator -/
  producerType : ProducerType

/-- Datatype containing metadata needed to derive a sub-checker
    that is invoked from the main checker function -/
structure SubCheckerInfo extends HandlerInfo where
  /-- `checkerSort` determines if the sub-generator is to be invoked
      when `size == 0` (i.e. it is a `BaseChecker`), or if it is to be invoked
      when `size > 0` (i.e. the sub-checker is inductively defined and makes
      recursive calls) -/
  checkerSort : CheckerSort

  /-- The constructor of an inductive relation corresponding to this sub-checker -/
  ctor : InductiveConstructor


/-- Converts an array of `Action`s into a `GroupedActions` -/
def mkGroupedActions (gccs: Array Action) : MetaM GroupedActions := do
  let mut gen_list := #[]
  let mut checkInductiveActions := #[]
  let mut checkNonInductiveActions := #[]
  let mut iflet_list := #[]
  let mut ret_list := #[]
  let mut variableEqs := #[]
  for gcc in gccs do
    match gcc with
    | .genFVar _ _
    | .genInputForInductive _ _ _ _ =>
        gen_list := gen_list.push gcc
    | .matchFVar _ hyp => {
        iflet_list := iflet_list.push gcc;
        gen_list := gen_list.push gcc;
        variableEqs := variableEqs ++ hyp.variableEqs
      }
    | .ret _ =>
        ret_list := ret_list.push gcc
    | .checkInductive _ =>
        checkInductiveActions := checkInductiveActions.push gcc
    | .checkNonInductive _ =>
        checkNonInductiveActions := checkNonInductiveActions.push gcc
  return {
    gen_list := gen_list
    checkInductiveActions := checkInductiveActions
    checkNonInductiveActions := checkNonInductiveActions
    iflet_list := iflet_list
    ret_list := ret_list
    variableEqs := variableEqs
  }


/-- Takes a constructor for an inductive relation, a list of argument names, the index of the argument we wish to generate (`genpos`),
    and returns a corresponding `SubCheckerInfo` for a checker -/
def mkSubCheckerInfoFromConstructor (ctor : InductiveConstructor)
  (inputNames : Array String) (nameMap : HashMap Name Name) : MetaM SubCheckerInfo := do
  let conclusion ← separateFVars ctor.conclusion ctor.localCtx
  let ctor := { ctor with localCtx := conclusion.localCtx }
  let args := conclusion.newHypothesis.getAppArgs
  let inputNamesAndArgs := inputNames.zip args
  let inputPairsThatNeedMatching := inputNamesAndArgs.filter (fun (_, arg) => !arg.isFVar)
  let (inputsToMatch, matchCases) := inputPairsThatNeedMatching.unzip
  let actions ← Actions_for_checker ctor
  let groupedActions ← mkGroupedActions actions.actions
  let checkerSort := if ctor.recursive_hypotheses.isEmpty then .BaseChecker else .InductiveChecker
  return {
    ctor := ctor
    inputs := inputNames
    inputsToMatch := inputsToMatch
    matchCases := matchCases
    groupedActions := groupedActions
    checkerSort := checkerSort
    localCtx := actions.localCtx
    variableEqs := conclusion.variableEqs ++ groupedActions.variableEqs
    nameMap := nameMap
  }

/-- Takes a constructor for an inductive relation, a list of argument names,
    the index of the argument we wish to generate (`idx`),
    and returns a corresponding `SubGeneratorInfo` for a generator -/
def mkSubGeneratorInfoFromConstructor (ctor : InductiveConstructor) (inputNames : Array String)
  (idx : Nat) (producerType : ProducerType) (nameMap : HashMap Name Name) : MetaM SubGeneratorInfo :=
  withLCtx' ctor.localCtx do
    let inputNamesList := inputNames.toList
    let tempFVar := Expr.fvar (← mkFreshFVarId)
    let conclusion_args := ctor.conclusion.getAppArgs.set! idx tempFVar
    let new_conclusion := mkAppN ctor.conclusion.getAppFn conclusion_args

    let conclusion ← separateFVars new_conclusion ctor.localCtx

    withDebugFlag globalDebugFlag do
      logInfo s!"conclusion before rewriting = {← ppExpr new_conclusion}"
      logInfo s!"conclusion after rewriting = {← ppExpr conclusion.newHypothesis}"

    let ctor := { ctor with localCtx := conclusion.localCtx }
    let args := ctor.conclusion.getAppArgs.toList
    let zippedInputsAndArgs := List.zip inputNamesList args

    -- Take all elements of `inputNamesAndArgs`, but omit the element at the `genpos`-th index
    let inputNamesAndArgs := List.eraseIdx zippedInputsAndArgs idx

    -- Find all pairs where the argument is not a free variable
    -- (these are the arguments that need matching)
    let inputPairsThatNeedMatching := inputNamesAndArgs.filter (fun (_, arg) => !arg.isFVar)
    let (inputsToMatch, matchCases) := inputPairsThatNeedMatching.unzip
    let actions ← Actions_for_producer ctor idx
    let groupedActions ← mkGroupedActions actions.actions

    -- Constructors with no hypotheses get `BaseGenerator`s
    -- (otherwise, the generator needs to make a recursive call and is thus inductively-defined)
    let generatorSort :=
      if ctor.recursive_hypotheses.isEmpty
        then .BaseGenerator
        else .InductiveGenerator

    withDebugFlag globalDebugFlag do
      logInfo s!"inside mkSubGeneratorInfoFromConstructor"
      logInfo s!"conclusion.variableEqs = {conclusion.variableEqs}"
      logInfo s!"groupedActions.variableEqs = {groupedActions.variableEqs}"

    return {
      inputs := (List.eraseIdx inputNamesList idx).toArray
      inputsToMatch := inputsToMatch.toArray
      matchCases := matchCases.toArray
      groupedActions := groupedActions
      generatorSort := generatorSort
      localCtx := actions.localCtx
      producerType := producerType
      variableEqs := conclusion.variableEqs ++ groupedActions.variableEqs
      nameMap := nameMap
    }

/-- Takes an `Expr` representing an inductive relation,
    a list of names `argNames` (arguments to the inductive relation),
    the index of the argument we wish to generate (`targetIdx`),
    and the desired `producerType` (`Generator` or `Enumerator`),
    and returns a collection of `SubGeneratorInfo`s for a producer -/
def getSubGeneratorInfos (inductiveRelation : Expr) (argNames : Array String) (targetIdx: Nat)
  (producerType : ProducerType) : MetaM (Array SubGeneratorInfo × LocalContext × HashMap Name Name) := do
  let inductiveInfo ← getInductiveInfoWithArgs inductiveRelation argNames
  let nameMap := inductiveInfo.nameMap
  let topLevelLocalCtx := inductiveInfo.localCtx
  let mut subGenerators := #[]
  for ctor in inductiveInfo.constructors do
    let subGenerator ← mkSubGeneratorInfoFromConstructor ctor argNames targetIdx producerType nameMap
    subGenerators := subGenerators.push subGenerator
  return (subGenerators, topLevelLocalCtx, nameMap)

/-- Takes an `Expr` representing an inductive relation and a list of names (arguments to the inductive relation),
    and returns a collection of `BacktrackElem`s for a checker -/
def getSubCheckerInfos (inductiveRelation : Expr) (argNames : Array String) : MetaM (Array SubCheckerInfo × LocalContext × HashMap Name Name) := do
  let inductiveInfo ← getInductiveInfoWithArgs inductiveRelation argNames
  let nameMap := inductiveInfo.nameMap
  let topLevelLocalCtx := inductiveInfo.localCtx
  let mut subCheckers := #[]
  for ctor in inductiveInfo.constructors do
    let subChecker ← mkSubCheckerInfoFromConstructor ctor argNames nameMap
    subCheckers := subCheckers.push subChecker
  return (subCheckers, topLevelLocalCtx, nameMap)


end Plausible.IR
