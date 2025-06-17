import Lean
import Plausible.IR.Constructor
import Plausible.New.Idents
import Plausible.New.TSyntaxCombinators

open Plausible.IR
open Lean Elab Command Meta Term Parser Std
open Idents

/-- `genInputForInductive fvar hyp idx generationStyle` produces a let-bind expression of the form
    based on the `generationStyle` specified:
    - If `generationStyle = .RecursiveCall`, we produce the term
      `let fvar ← aux_arb size e1 … en`, where `e1, …, en` are the arguments to the
      a hypothesis `hyp` for an inductive relation with the argument at index `idx` removed
      (since `fvar` is the argument at index `idx`, and we are generating `fvar`)
    - If `generationStyle = .TypeClassresolution`, we produce the term
      `let fvar ← GenSuchThat.genST (fun fvar => hyp)`, i.e.
      we use typeclass resolution to invoke the generator from the
      `GenSuchThat.genST` which produces values satisfying the hypothesis `hyp`
      (note: this requires that such an typeclass instance already exists). -/
def genInputForInductive (fvar : FVarId) (hyp : Expr) (idx : Nat) (generationStyle : GenerationStyle) : MetaM (TSyntax `doElem) := do
  let argExprs := hyp.getAppArgs.eraseIdx! idx
  let argTerms ← Array.mapM PrettyPrinter.delab argExprs
  let lhs := mkIdent $ fvar.name

  let hypTerm ← PrettyPrinter.delab hyp
  let generatorConstraint ← `((fun $lhs:ident => $hypTerm))

  let rhsTerms :=
    match generationStyle with
    | .RecursiveCall => #[auxArbFn, initSizeIdent, mkIdent `size'] ++ argTerms
    | .TypeClassResolution => #[qualifiedGenSizedSTIdent, generatorConstraint]

  mkLetBind lhs rhsTerms

/-- Constructs an anonymous sub-generator. See the comments in the body of this function
    for details on how this sub-generator is created. -/
def mkSubGenerator (subGenerator : SubGeneratorInfo) : TermElabM (TSyntax `term) := do
  let mut doElems := #[]

  for action in subGenerator.groupedActions.gen_list do
    match action with
    | .genInputForInductive fvar hyp idx style =>
      -- Recursively invoke the generator to generate an argument for the hypothesis `hyp` at index `idx`,
      -- then bind the generated value to the free variable `fvar`
      let bindExpr ← liftMetaM $ genInputForInductive fvar hyp idx style
      doElems := doElems.push bindExpr
    | .genFVar fvar ty =>
      -- Generate a value of type `ty`, then bind it to `fvar`
      let typeSyntax ← PrettyPrinter.delab ty
      let bindExpr ← mkLetBind (mkIdent fvar.name) #[interpSampleFn, typeSyntax]
      doElems := doElems.push bindExpr
    | _ => continue

  -- Check that all hypotheses which are not `inductive`s are upheld when we generate free variables
  let mut nonInductiveHypothesesToCheck := #[]
  for action in subGenerator.groupedActions.checkNonInductiveActions do
    if let .checkNonInductive predicateExpr := action then
      let predicateTerm ← PrettyPrinter.delab predicateExpr
      nonInductiveHypothesesToCheck := nonInductiveHypothesesToCheck.push predicateTerm

  -- TODO: invoke checkers for auxiliary inductive relations (for `checkInductive` actions)
  -- ^^ invoke `DecOpt.decOpt` here somehow

  let mut inductiveHypothesesToCheck := #[]
  for action in subGenerator.groupedActions.checkInductiveActions do
    if let .checkInductive inductiveExpr := action then
      let inductiveTerm ← PrettyPrinter.delab inductiveExpr
      inductiveHypothesesToCheck := inductiveHypothesesToCheck.push inductiveTerm

  logInfo "**********************"
  logInfo m!"nonInductiveHypothesesToCheck = {nonInductiveHypothesesToCheck}"
  logInfo m!"inductivesToCheck = {inductiveHypothesesToCheck}"
  logInfo "**********************"

  -- TODO: change `groupedActions.ret_list` to a single element since each do-block can only
  -- have one (final) `return` expression
  let returnList := subGenerator.groupedActions.ret_list
  let action := returnList[0]?
  if let some action' := action then
    match action' with
    | .ret expr =>
      -- Delaborate `expr` to get a `TSyntax` for the argument we're generating
      let argToGenTerm ← PrettyPrinter.delab expr

      -- If any let-bind expressions have already appeared,
      -- then append `return $argToGenTerm` to the end of the do-block
      let generatorBody ←
        if !doElems.isEmpty then
          let retExpr ← `(doElem| return $argToGenTerm:term)
          -- Check that all hypotheses are satisfied before returning the generated value
          if !nonInductiveHypothesesToCheck.isEmpty then
            let ifExpr ← mkIfExprWithNaryAnd nonInductiveHypothesesToCheck retExpr (← `(doElem| $failFn:term))
            doElems := doElems.push ifExpr
          else
            -- No hypotheses to check, we can just return the generated value directly
            doElems := doElems.push retExpr

          -- Create a monadic `do`-block containing all the exprs above
          mkDoBlock doElems

        -- No let-bind expressions have appeared in the do-block,
        -- so we can just create `pure $argToGenTerm` without needing
        -- to create a do-block
        else
          `($pureIdent $argToGenTerm:term)

      -- If there are inputs on which we need to perform a pattern-match,
      -- create a pattern-match expr which only returns the generator body
      -- if the match succeeds
      if !subGenerator.inputsToMatch.isEmpty then
        let mut cases := #[]
        -- For now, we assume there is only one scrutinee
        let scrutinee := mkIdent $ Name.mkStr1 subGenerator.inputsToMatch[0]!

        for patternExpr in subGenerator.matchCases do
          -- TODO: if the scrutinee appears in the pattern, rename the pattern to avoid name clashes?
          -- Right now, the derived generator works due to shadowing, but not sure if we should judiciously rename
          -- free variables in the `generatorBody` (this would be somewhat laborious)
          let pattern ← PrettyPrinter.delab patternExpr
          let case ← `(Term.matchAltExpr| | $pattern:term => $generatorBody:term)
          cases := cases.push case

        let catchAllCase ← `(Term.matchAltExpr| | _ => $failFn)
        cases := cases.push catchAllCase

        mkMatchExpr scrutinee cases
      else
        return generatorBody

    | _ => throwUnsupportedSyntax

  else
    throwUnsupportedSyntax

/-- Computes the weight of a generator
    - `BaseGenerator`s are assigned weight 1
    - `InductiveGenerator`s are assigned weight `Nat.succ size'`
      (for the case when the top-level generator's `size` parameter is non-zero) -/
def getGeneratorWeight (gen : SubGeneratorInfo) : TermElabM (TSyntax `term) := do
  match gen.generatorSort with
  | .BaseGenerator => `(1)
  | .InductiveGenerator => `($(mkIdent ``Nat.succ) $(mkIdent `size'))

/-- Constructs a list of weighted thunked sub-generators as a Lean term -/
def mkWeightedThunkedSubGenerators (subGeneratorInfos : Array SubGeneratorInfo) (generatorSort : GeneratorSort) : TermElabM (TSyntax `term) := do
  let subGenerators ← Array.mapM mkSubGenerator subGeneratorInfos
  let generatorWeights ← Array.mapM getGeneratorWeight subGeneratorInfos

  let mut weightedGenerators := #[]

  for (weight, generatorBody) in Array.zip generatorWeights subGenerators do
    let thunkedGenerator ← `(($weight, $thunkGenFn (fun _ => $generatorBody)))
    weightedGenerators := weightedGenerators.push thunkedGenerator

  -- Add generator that always fails for the case when `size == 0`
  -- (to represent running out of fuel / inability to synthesize a generator)
  if let .BaseGenerator := generatorSort then
    weightedGenerators := weightedGenerators.push (← `((1, $thunkGenFn (fun _ => $failFn))))

  `([$weightedGenerators,*])
