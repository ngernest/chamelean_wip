import Lean
import Plausible.IR.Constructor
import Plausible.New.Idents


open Plausible.IR
open Lean Elab Command Meta Term Parser Std
open Idents

/-- Produces a trivial generator (e.g. `pure Leaf`)
    when all fields of a `GroupedActions` struct are empty except `ret_list` -/
def mkTrivialGenerator (GroupedActions : GroupedActions) : MetaM (TSyntax `term) := do
  let nonTrivialTerms := GroupedActions.gen_list ++ GroupedActions.iflet_list ++ GroupedActions.check_IR_list ++ GroupedActions.check_nonIR_list
  if not nonTrivialTerms.isEmpty then
    `([])
  else
    let mut generators := #[]
    for Action in GroupedActions.ret_list do
        if let .ret expr := Action then
          let argToGenTerm ← PrettyPrinter.delab expr
          let generatorBody ← `(fun _ => $pureIdent $argToGenTerm)
          let thunkedGenerator ← `((1, $thunkGenFn ($generatorBody)))
          generators := generators.push thunkedGenerator

    -- Convert the list of generator terms into a Lean list containing all the generators
    `([$generators,*])

/-- Constructs a Lean monadic `do` block out of an array of `doSeq`s
    (expressions that appear in the `do` block) -/
def mkDoBlock (doBlockExprs : TSyntaxArray ``Term.doSeq) : MetaM (TSyntax `term) := do
  let doBlockBody ← `(doSeq| $(TSyntaxArray.mk doBlockExprs)*)
  `(do $doBlockBody)

/-- `mkLetBind lhs rhsTerms` constructs a monadic let-bind expression of the form
    `let lhs ← e0 e1 … en`, where `rhsTerms := #[e0, e1, …, en]`.
    - Note: `rhsTerms` cannot be empty, otherwise this function throws an exception -/
def mkLetBind (lhs : Ident) (rhsTerms : TSyntaxArray `term) : MetaM (TSyntax ``Term.doSeq) := do
  let rhsList := rhsTerms.toList
  match rhsList with
  | f :: args =>
    `(doSeq| let $lhs:term ← $f:term $(args.toArray)*)
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

/-- Constructs a do-block for a sub-generator
    (TODO: figure out how to call this function in the rest of the command elaborator) -/
def mkDoBlockForSubGenerator (subGenerator : SubGeneratorInfo) : MetaM (TSyntax `term) := do
  let mut doBlockExprs := #[]
  for action in subGenerator.groupedActions.gen_list do
    match action with
    | .genInputForInductive fvar hyp idx =>
      let bindExpr ← genInputForInductive fvar hyp idx
      doBlockExprs := doBlockExprs.push bindExpr
    | _ => continue

  for action in subGenerator.groupedActions.ret_list do
    if let .ret expr := action then
      let argToGenTerm ← PrettyPrinter.delab expr
      let retExpr ← `(doSeq| $pureIdent:term $argToGenTerm:term)
      doBlockExprs := doBlockExprs.push retExpr

  mkDoBlock doBlockExprs


-- -- TODO: implement variant of `mkGeneratorFunction` that takes as its argument an `Array` of `SubGeneratorInfo`s
-- def mkSubGenerators (subGeneratorInfos : Array SubGeneratorInfo) : Bool := false
