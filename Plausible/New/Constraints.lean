import Lean
import Plausible.IR.Constructor
import Plausible.New.Idents


open Plausible.IR
open Lean Elab Command Meta Term Parser Std
open Idents

/-- Constructs a Lean monadic `do` block out of an array of `doSeq`s
    (expressions that appear in the `do` block) -/
private def mkDoBlock (doBlockExprs : TSyntaxArray ``Term.doSeq) : MetaM (TSyntax `term) := do
  let doSeqElems := TSyntaxArray.mk doBlockExprs
  let doBlockBody ← `(doSeq| $doSeqElems*)
  `(do $doBlockBody)

/-- `mkLetBind lhs rhsTerms` constructs a monadic let-bind expression of the form
    `let lhs ← e0 e1 … en`, where `rhsTerms := #[e0, e1, …, en]`.
    - Note: `rhsTerms` cannot be empty, otherwise this function throws an exception -/
private def mkLetBind (lhs : Ident) (rhsTerms : TSyntaxArray `term) : MetaM (TSyntax ``Term.doSeq) := do
  let rhsList := rhsTerms.toList
  match rhsList with
  | f :: args =>
    let argTerms := args.toArray
    `(doSeq| let $lhs:term ← $f:term $argTerms*; )
  | [] => throwError "rhsTerms can't be empty"

/-- `genInputForInductive fvar hyp idx` produces a let-bind expression of the form
    `let fvar ← aux_arb size e1 … en`, where `e1, …, en` are the arguments to the
    a hypothesis `hyp` for an inductive relation with the argument at index `idx` removed
    (since `fvar` is the argument at index `idx`, and we are generating `fvar`) -/
def genInputForInductive (fvar : FVarId) (hyp : Expr) (idx : Nat) : MetaM (TSyntax ``Term.doSeq) := do
  let argExprs := hyp.getAppArgs.eraseIdx! idx
  let argTerms ← Array.mapM PrettyPrinter.delab argExprs
  let lhs := mkIdent $ fvar.name
  let rhsTerms := #[auxArbFn, sizeIdent] ++ argTerms
  mkLetBind lhs rhsTerms


/-- Constructs an anonymous sub-generator -/
def mkSubGenerator (subGenerator : SubGeneratorInfo) : TermElabM (TSyntax `term) := do
  let mut doBlockExprs := #[]

  for action in subGenerator.groupedActions.gen_list do
    match action with
    | .genInputForInductive fvar hyp idx =>
      let bindExpr ← liftMetaM $ genInputForInductive fvar hyp idx
      doBlockExprs := doBlockExprs.push bindExpr
    | _ => continue

  let returnList := subGenerator.groupedActions.ret_list
  let action := returnList[0]?
  if let some action' := action then
    if let .ret expr := action' then
      let argToGenTerm ← PrettyPrinter.delab expr
      let retExpr ← `(doSeq| return $argToGenTerm:term)
      doBlockExprs := doBlockExprs.push retExpr
      mkDoBlock doBlockExprs
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

    -- TODO: replace `failFn` with generatorBody

    let thunkedGenerator ← `((1, $thunkGenFn (fun _ => $failFn)))
    weightedGenerators := weightedGenerators.push thunkedGenerator

  `([$weightedGenerators,*])
