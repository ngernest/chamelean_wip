import Lean
import Plausible.IR.Constructor
import Plausible.New.Idents
import Plausible.New.DoBlocks

open Plausible.IR
open Lean Elab Command Meta Term Parser Std
open Idents


/-- `genInputForInductive fvar hyp idx` produces a let-bind expression of the form
    `let fvar ← aux_arb size e1 … en`, where `e1, …, en` are the arguments to the
    a hypothesis `hyp` for an inductive relation with the argument at index `idx` removed
    (since `fvar` is the argument at index `idx`, and we are generating `fvar`) -/
def genInputForInductive (fvar : FVarId) (hyp : Expr) (idx : Nat) : MetaM (TSyntax `doElem) := do
  let argExprs := hyp.getAppArgs.eraseIdx! idx
  let argTerms ← Array.mapM PrettyPrinter.delab argExprs
  let lhs := mkIdent $ fvar.name
  let rhsTerms := #[auxArbFn, sizeIdent] ++ argTerms
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

  let returnList := subGenerator.groupedActions.ret_list
  let action := returnList[0]?
  if let some action' := action then
    if let .ret expr := action' then
      let argToGenTerm ← PrettyPrinter.delab expr
      let retExpr ← `(doElem| return $argToGenTerm:term)
      doElems := doElems.push retExpr
      mkDoBlock doElems
    else
      throwUnsupportedSyntax
  else
    throwUnsupportedSyntax


/-- Constructs a list of weighted thunked sub-generators as a Lean term -/
def mkWeightedThunkedSubGenerators (subGeneratorInfos : Array SubGeneratorInfo) : TermElabM (TSyntax `term) := do
  let subGenerators ← Array.mapM mkSubGenerator subGeneratorInfos
  let mut weightedGenerators := #[]

  -- TODO: find a way of figuring out what the right weight is
  for generatorBody in subGenerators do

    logInfo m!"generatorBody = {generatorBody}"

    let thunkedGenerator ← `((1, $thunkGenFn (fun _ => $generatorBody)))
    weightedGenerators := weightedGenerators.push thunkedGenerator

  `([$weightedGenerators,*])
