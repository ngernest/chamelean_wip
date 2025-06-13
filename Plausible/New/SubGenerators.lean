import Lean
import Plausible.IR.Constructor
import Plausible.New.Idents
import Plausible.New.DoBlocks

open Plausible.IR
open Lean Elab Command Meta Term Parser Std
open Idents

-- TODOs:
-- 1. Figure out how to sort the subgenerators into ones to use when `size == 0` & ones to use when `size != 0`
-- ^^ look at how Thanh's code achieves this
-- 2. Figure out how to compute the weight of each subgenerator
-- ^^ may need to ask the QuickChick folks how they do this??


/-- `genInputForInductive fvar hyp idx` produces a let-bind expression of the form
    `let fvar ← aux_arb size e1 … en`, where `e1, …, en` are the arguments to the
    a hypothesis `hyp` for an inductive relation with the argument at index `idx` removed
    (since `fvar` is the argument at index `idx`, and we are generating `fvar`) -/
def genInputForInductive (fvar : FVarId) (hyp : Expr) (idx : Nat) : MetaM (TSyntax `doElem) := do
  let argExprs := hyp.getAppArgs.eraseIdx! idx
  let argTerms ← Array.mapM PrettyPrinter.delab argExprs
  let lhs := mkIdent $ fvar.name
  let rhsTerms := #[auxArbFn, mkIdent `size'] ++ argTerms
  mkLetBind lhs rhsTerms


/-- Constructs an anonymous sub-generator -/
def mkSubGenerator (subGenerator : SubGeneratorInfo) : TermElabM (TSyntax `term) := do
  let mut doElems := #[]

  for action in subGenerator.groupedActions.gen_list do
    match action with
    | .genInputForInductive fvar hyp idx =>
      let bindExpr ← liftMetaM $ genInputForInductive fvar hyp idx
      doElems := doElems.push bindExpr
    | .genFVar fvar ty =>
      let typeSyntax ← PrettyPrinter.delab ty
      let bindExpr ← mkLetBind (mkIdent fvar.name) #[interpSampleFn, typeSyntax]
      doElems := doElems.push bindExpr
    | _ => continue

  -- TODO: change `groupedActions.ret_list` to a single element since each do-block can only
  -- have one (final) `return` expression
  let returnList := subGenerator.groupedActions.ret_list
  let action := returnList[0]?
  if let some action' := action then
    if let .ret expr := action' then
      let argToGenTerm ← PrettyPrinter.delab expr
      -- If any let-bind expressions have already appeared,
      -- then append `return $argToGenTerm` to the end of the do-block
      if not doElems.isEmpty then
        let retExpr ← `(doElem| return $argToGenTerm:term)
        doElems := doElems.push retExpr
        mkDoBlock doElems
      -- No let-bind expressions have appeared in the do-block,
      -- so we can just create `pure $argToGenTerm` without needing
      -- to create a do-block
      else
        `($pureIdent $argToGenTerm:term)
    else
      throwUnsupportedSyntax
  else
    throwUnsupportedSyntax


/-- Constructs a list of weighted thunked sub-generators as a Lean term -/
def mkWeightedThunkedSubGenerators (subGeneratorInfos : Array SubGeneratorInfo) (generatorSort : GeneratorSort) : TermElabM (TSyntax `term) := do
  let subGenerators ← Array.mapM mkSubGenerator subGeneratorInfos
  let mut weightedGenerators := #[]

  -- TODO: find a way of figuring out what the right weight is
  for generatorBody in subGenerators do

    logInfo m!"generatorBody = {generatorBody}"

    let thunkedGenerator ← `((1, $thunkGenFn (fun _ => $generatorBody)))
    weightedGenerators := weightedGenerators.push thunkedGenerator

  -- Add generator that always fails for the case when `size == 0`
  -- (to represent running out of fuel / inability to synthesize a generator)

  if let .BaseGenerator := generatorSort then
    weightedGenerators := weightedGenerators.push (← `((1, $thunkGenFn (fun _ => $failFn))))

  `([$weightedGenerators,*])
