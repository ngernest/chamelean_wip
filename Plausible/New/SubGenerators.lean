import Lean
import Plausible.New.Utils
import Plausible.IR.Constructor
import Plausible.New.Idents
import Plausible.New.TSyntaxCombinators

open Plausible.IR
open Lean Elab Command Meta Term Parser Std
open Idents


/-- `genInputForInductive fvar hyp idx generationStyle producerType` produces a let-bind expression of the form
    based on the specified `generationStyle` and `producerType`:
    - If `generationStyle = .RecursiveCall`, we produce the term
      `let fvar ← aux_arb size e1 … en`, where `e1, …, en` are the arguments to the
      a hypothesis `hyp` for an inductive relation with the argument at index `idx` removed
      (since `fvar` is the argument at index `idx`, and we are generating `fvar`)
      + If `producerType = .Generator`, we call `aux_arb` (the inner function in a derived generator)
      + If `producerType = .Enumerator`, we call `aux_enum` (the inner function in a derived generator)
    - If `generationStyle = .TypeClassResolution` and `producerType = .Generator`, we produce the term
      `let fvar ← ArbitrarySuchThat.arbitraryST (fun fvar => hyp)`, i.e.
      we use typeclass resolution to invoke the generator from the typeclass function
      `ArbitrarySuchThat.arbitraryST` which produces values satisfying the hypothesis `hyp`
      (note: this requires that such an typeclass instance already exists)
      + If `producerType = .Enumerator`, we produce a similar term, but we call `EnumSuchThat.enumST` instead -/
def genInputForInductive (fvar : FVarId) (hyp : Expr) (idx : Nat) (generationStyle : GenerationStyle) (producerType : ProducerType) (localCtx : LocalContext) : MetaM (TSyntax `doElem) := do
  let argExprs := hyp.getAppArgs.eraseIdx! idx
  let argTerms ← Array.mapM (delabExprInLocalContext localCtx) argExprs
  let lhs := Lean.mkIdent $ getUserNameInContext localCtx fvar

  let hypTerm ← delabExprInLocalContext localCtx hyp
  let producerConstraint ← `((fun $lhs:ident => $hypTerm))

  let recursiveProducerFn :=
    match producerType with
    | .Generator => auxArbFn
    | .Enumerator => auxEnumFn

  let producerTypeclassFn :=
    match producerType with
    | .Generator => arbitrarySTFn
    | .Enumerator => enumSTFn

  let rhsTerms :=
    match generationStyle with
    | .RecursiveCall => #[recursiveProducerFn, initSizeIdent, mkIdent `size'] ++ argTerms
    | .TypeClassResolution => #[producerTypeclassFn, producerConstraint]

  mkLetBind lhs rhsTerms

/-- Constructs a pattern match which checks whether all the equalities in `variableEqualities` hold
    (using the `DecOpt` instance when performing the equality check), and if so, producing
    the `retExpr`, otherwise failing (i.e. returning `OptionT.fail`)

    For example, if `variableEqualities := [(t, t0)]`, then the following match expression is produced:
    ```
    match DecOpt.decOpt (t = t0) initSize with
    | some true => $retExpr
    | _ => OptionT.fail
    ```
   - Precondition: `variableEqualities` must be non-empty
   - TODO: we assume `variableEqualities` has length 1 right now -- generalize this function
     to handle any length! -/
def mkVariableEqualityCheckMatchExpr (syntaxKind : SyntaxNodeKind) (variableEqualities : TSyntaxArray `term)
  (retExpr : TSyntax `term) : TermElabM (TSyntax syntaxKind) := do



  let equality := variableEqualities[0]!
  IO.println "inside mkVariableEqualityCheckMatchExpr"
  IO.println s!"equality = {equality}"

  let scrutinee ← `($decOptFn:ident ($equality) $initSizeIdent)

  let trueCase ← `(Term.matchAltExpr| | $(mkIdent ``some) $(mkIdent ``true) => $retExpr:term)
  let catchAllCase ← `(Term.matchAltExpr| | _ => $failFn)
  let cases := #[trueCase, catchAllCase]
  match syntaxKind with
  | `doElem => mkDoElemMatchExpr scrutinee cases
  | `term => mkMatchExprWithScrutineeTerm scrutinee cases
  | _ => throwError "Unexpected SyntaxNodeKind: expected either a `doElem or a `term"

/-- Creates the body of the sub-generator consisting of a monadic `do`-block and any extra pattern-matches
    to check non-inductive hypotheses / variable equalities. The arguments are:
    - `doBlock`: an ordered list of expressions in the `do`-block that have been created so far
    - `argToGenTerm`: the term `e` to be `return`-ed at the end of the `do`-block via the term `return e`
    - `nonInductiveHypothesesToCheck`: hypotheses which are not inductive relations that need to be checked
       (by invoking their `DecOpt` instance) prior to `return`ing the generated value
    - `variableEqualitiesToCheck`: equalities between variables `v1, v2` that need to be checked
      (by invoking the `DecOpt` instance for the proposition `v1 = v2`) prior to `return`ing the generated value -/
def mkSubGeneratorBody (doBlock : TSyntaxArray `doElem) (argToGenTerm : Term) (nonInductiveHypothesesToCheck : Array Term)
  (variableEqualitiesToCheck : TSyntaxArray `term) : TermElabM (TSyntax `term) := do
  let mut doElems := doBlock
  if !doElems.isEmpty then {
    let retExpr ← `(doElem| return $argToGenTerm:term)

    -- Check that all hypotheses are satisfied before returning the generated value
    if !nonInductiveHypothesesToCheck.isEmpty then {
      let ifExpr ← mkIfExprWithNaryAnd nonInductiveHypothesesToCheck retExpr (← `(doElem| $failFn:term))
      doElems := doElems.push ifExpr
    } else {
      if !variableEqualitiesToCheck.isEmpty then {
        -- Check that the equalities in `variableEqualitiesToCheck` hold (via creating a pattern match)
        let matchExpr ← mkVariableEqualityCheckMatchExpr `doElem variableEqualitiesToCheck (← mkDoBlock #[retExpr])
        doElems := doElems.push matchExpr
      } else {
        -- No hypotheses to check, we can just return the generated value directly
        doElems := doElems.push retExpr
      }
    }
    -- Create a monadic `do`-block containing all the exprs above
    mkDoBlock doElems

  -- No let-bind expressions have appeared in the do-block,
  -- so we can just create `pure $argToGenTerm` without needing
  -- to create a do-block
  } else {
    IO.println "inside mkSubGeneratorBody, doElems is empty"

    let retExpr ← `($pureFn $argToGenTerm:term)
    -- If there are any variable equalities that we need to check,
    -- create a match expression before doing `pure $argToGenTerm`
    if !variableEqualitiesToCheck.isEmpty then {
      mkVariableEqualityCheckMatchExpr `term variableEqualitiesToCheck retExpr
    } else {
      pure retExpr
    }
  }

/-- Creates let-bind expressions of the form `let x ← ...` inside a monadic do-block, where the RHS
    of the let-bind expr is a call to some monadic producer (generator or producer).
    The `producerType` argument determines whether a generator or an enumerator should be invoked,
    while `actions` is used to determine whether we sample an unconstrained value (e.g. by calling
    `Arbitrary.arbitrary` or `Enum.enum`), or if we should invoke a constrained producer
    by calling the producer associated with the `ArbitrarySuchThat` or `EnumSuchThat` instance
    for the constrianing proposition. -/
def mkLetBindExprsInDoBlock (actions : Array Action) (producerType : ProducerType) (localCtx : LocalContext) : TermElabM (TSyntaxArray `doElem) := do
  let mut doElems := #[]

  for action in actions do
    match action with
    | .genInputForInductive fvar hyp idx style =>
      -- Recursively invoke the producer to sample an argument for the hypothesis `hyp` at index `idx`,
      -- then bind the produced value to the free variable `fvar`
      let bindExpr ← liftMetaM $ genInputForInductive fvar hyp idx style producerType localCtx
      doElems := doElems.push bindExpr
    | .genFVar fvar _ =>
      -- Sample a value from an unconstrained producer using `arbitrary` / `enum`, then bind it to `fvar`
      let producerFn :=
        match producerType with
        | .Generator => arbitraryFn
        | .Enumerator => enumFn
      let bindExpr ← mkLetBind (Lean.mkIdent $ getUserNameInContext localCtx fvar) #[producerFn]
      doElems := doElems.push bindExpr
    | _ => continue

  return doElems


/-- Constructs an anonymous sub-generator. See the comments in the body of this function
    for details on how this sub-generator is created. -/
def mkSubGenerator (subGenerator : SubGeneratorInfo) : TermElabM (TSyntax `term) := do

  -- Create a monadic do-block containing all the calls to other producers (in the form of let-bind expressions)
  let doElems ← mkLetBindExprsInDoBlock subGenerator.groupedActions.gen_list subGenerator.producerType subGenerator.localCtx

  -- Check that all hypotheses which are not `inductive`s are upheld when we generate free variables
  let mut nonInductiveHypothesesToCheck := #[]
  for action in subGenerator.groupedActions.checkNonInductiveActions do
    if let .checkNonInductive predicateExpr := action then
      let ty ← inferType predicateExpr

      -- Check if the predicate is a `Prop` (i.e. `Sort 0`)
      if ty.isProp then
        -- If yes, add it to our list of hypotheses to check using the `DecOpt` instance
        -- for that particular `Prop`
        let predicateTerm ← delabExprInLocalContext subGenerator.localCtx predicateExpr
        nonInductiveHypothesesToCheck := nonInductiveHypothesesToCheck.push predicateTerm
      else if ty == mkSort levelOne then
        -- `predicateExpr` is a `Type` (i.e. `Type 0`, the usual universe level for ordinary types)
        -- TODO: just call the `SampleableExt` instance for the `Type`
        logWarning m!"encountered Type instead of Prop"
      else
        -- `predicateExpr` is `Type u` for some `u >= 1` (some higher universe level)
        throwError m!"{predicateExpr} has universe level {ty}, which is not supported"

  let mut inductiveHypothesesToCheck : TSyntaxArray `term := #[]
  for action in subGenerator.groupedActions.checkInductiveActions do
    if let .checkInductive inductiveExpr := action then
      -- Convert the `Expr` into a `Term` using the info about free variables stored in the current `LocalContext`
      let inductiveTerm ← delabExprInLocalContext subGenerator.localCtx inductiveExpr

      -- Conver the `Term` into a `TSyntax term`
      let typedInductiveTerm ← `($inductiveTerm:term)

      inductiveHypothesesToCheck := inductiveHypothesesToCheck.push typedInductiveTerm

  -- Add equality checks for any pairs of variables in `variableEqualities`
  IO.println "inside mkSubGenerator"
  IO.println s!"subGenerator.variableEqs = {subGenerator.variableEqs}"

  let mut variableEqualitiesToCheck ← Array.mapM (fun e => delabExprInLocalContext subGenerator.localCtx e) subGenerator.variableEqs

  IO.println s!"variableEqualitiesToCheck = {variableEqualitiesToCheck}"

  -- TODO: change `groupedActions.ret_list` to a single element since each do-block can only
  -- have one (final) `return` expression
  let returnList := subGenerator.groupedActions.ret_list
  let action := returnList[0]?
  if let some action' := action then
    match action' with
    | .ret expr =>
      -- Delaborate `expr` to get a `TSyntax` for the argument we're generating
      let argToGenTerm ← delabExprInLocalContext subGenerator.localCtx expr

      -- Create the body of the sub-generator consisting of a monadic do-block and any extra pattern-matches
      -- to check non-inductive hypotheses / variable equalities
      let generatorBody ← mkSubGeneratorBody doElems argToGenTerm nonInductiveHypothesesToCheck variableEqualitiesToCheck

      -- TODO: invoke checkers for auxiliary inductive relations (for `checkInductive` actions)
      -- ^^ invoke `DecOpt.decOpt` here somehow

      -- If there are inputs on which we need to perform a pattern-match,
      -- create a pattern-match expr which only returns the generator body
      -- if the match succeeds
      if !subGenerator.inputsToMatch.isEmpty then
        let mut cases := #[]

        -- Handle multiple scrutinees by giving all of them fresh names
        -- Use the name map to lookup the freshened versions of the scrutinee's name
        let existingNames := Name.mkStr1 <$> subGenerator.inputsToMatch
        let scrutinees := (lookupFreshenedNameInNameMap subGenerator.nameMap existingNames) <$> existingNames

        -- Construct the match expression based on the info in `matchCases`
        let patterns ← Array.mapM (fun patternExpr => delabExprInLocalContext subGenerator.localCtx patternExpr) subGenerator.matchCases
        -- If there are multiple scrutinees, the LHS of each case is a tuple containing the elements in `matchCases`
        let case ← `(Term.matchAltExpr| | $[$patterns:term],* => $generatorBody:term)
        cases := cases.push case

        -- The LHS of the catch-all case contains a tuple consisting entirely of wildcards
        let numScrutinees := Array.size scrutinees
        let wildcards := Array.replicate numScrutinees (← `(_))
        let catchAllCase ← `(Term.matchAltExpr| | $wildcards:term,* => $failFn)
        cases := cases.push catchAllCase

        -- Create a pattern match that simultaneously matches on all the scrutinees
        mkSimultaneousMatch scrutinees cases

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
def mkWeightedThunkedSubGenerators (subGeneratorInfos : Array SubGeneratorInfo)
  (generatorSort : GeneratorSort) : TermElabM (TSyntax `term) := do
  let subGenerators ← Array.mapM mkSubGenerator subGeneratorInfos
  let generatorWeights ← Array.mapM getGeneratorWeight subGeneratorInfos

  let mut weightedGenerators := #[]

  for (weight, generatorBody) in Array.zip generatorWeights subGenerators do
    let thunkedGenerator ← `(($weight, $OptionTThunkGenFn (fun _ => $generatorBody)))
    weightedGenerators := weightedGenerators.push thunkedGenerator

  -- Add generator that always fails for the case when `size == 0`
  -- (to represent running out of fuel / inability to synthesize a generator)
  if let .BaseGenerator := generatorSort then
    weightedGenerators := weightedGenerators.push (← `((1, $OptionTThunkGenFn (fun _ => $failFn))))

  `([$weightedGenerators,*])
