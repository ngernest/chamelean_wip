import Lean
import Plausible.IR.Constructor
import Plausible.IR.Extractor
import Plausible.New.Idents
import Plausible.New.TSyntaxCombinators
import Plausible.New.Utils

open Plausible.IR
open Idents
open Lean Elab Command Meta Term Parser Std


/-- The `CheckerStyle` datatype describes the "style" in which a style should be invoked:
    - `RecursiveCall` indicates that we should recursively call the current checker function
    - `TypeClassResolution` indicates that we should call the generator via typeclass resolution
      (i.e. call the checker provided by the `DecOpt` instance for the proposition) -/
inductive CheckerStyle
  | RecursiveCall
  | TypeClassResolution
  deriving Repr

/-- `mkAuxiliaryCheckerCall hyp checkerStyle localCtx` creates a Lean term representing a call to a
    checker that determines whether the hypothesis `hyp` holds (note that `hyp` should be fully applied).
    - The `localCtx` argument is used for delaboration purposes (so that free variables are properly associated with their user-facing names).
    - The `checkerStyle` argument is used to determine the style in which the checker call should be performed
    - If `checkerStyle = .RecursiveCall`, we produce the term
    `aux_dec initSize size' (<hyp>)`, i.e. we perform a recursive call to the parent `aux_dec` function
    - If `checkerStyle = .TypeClassResolution`, we produce the term
    `DecOpt.decOpt (<hyp>) initSize`, i.e. we  use typeclass resolution to invoke the checker from the typeclass function
    `DecOpt.decOpt` which determines whether `hyp` holds -/
def mkAuxiliaryCheckerCall (hyp : Expr) (checkerStyle : CheckerStyle) (localCtx : LocalContext) : MetaM (TSyntax `term) := do
  let hypTerm ← delabExprInLocalContext localCtx hyp.getAppFn

  let argExprs := hyp.getAppArgs
  let argTerms ← Array.mapM (delabExprInLocalContext localCtx) argExprs

  match checkerStyle with
  | .RecursiveCall => `($auxDecFn $initSizeIdent $(mkIdent `size') $argTerms*)
  | .TypeClassResolution => `($decOptFn ($hypTerm $argTerms*) $initSizeIdent)

/-- `mkSubCheckerBody hypothesesToCheck ctor producerActions` constructs terms representing
    calls to checkers corresponding to the hypotheses in `hypothesesToCheck`
    (these are either recursive calls to the current checker function, or invocations of
    the `DecOpt` typeclass instance for the hypotheses)
    - `ctor` is the constructor of the inductive relation corresponding to
      the sub-checker being built
    - `producerActions` contains a list of producer actions
      (to be turned into enumerator calls by resolving instances of the `EnumSuchThat` or `Enum` enumerator typeclasses)
    - It is the caller's responsibility to ensure that:
      + `hypothesesToCheck` only contains `Action`s created using the `.checkInductive` or `.checkNonInductive` constructors,
      + `producerActions` only contains `Action`s created using the `.genInputForInductive` or `.genFVar` constructors
    - See the comments in the body of this function for further details -/
def mkSubCheckerBody (hypothesesToCheck : List Action) (ctor : InductiveConstructor) (producerActions : List Action) : TermElabM (TSyntax `term) :=
  if hypothesesToCheck.isEmpty then
    `($someFn:ident $trueIdent:ident)
  else
    match producerActions with
    | [] => do
      let mut callsToOtherCheckers := #[]

      for hypothesis in hypothesesToCheck do
        match hypothesis with
        | .checkInductive hyp | .checkNonInductive hyp =>
          -- Check if the hypothesis mentions the current inductive relation
          -- If yes, perform a recursive call to the parent checker
          -- Otherwise, perform typeclass resolution & invoke the checker provided by the `DecOpt` instance for the proposition
          let checkerStyle := if hypothesisRecursivelyCallsCurrentInductive hyp ctor then .RecursiveCall else .TypeClassResolution
          let checkerCall ← mkAuxiliaryCheckerCall hyp checkerStyle ctor.localCtx
          callsToOtherCheckers := callsToOtherCheckers.push checkerCall
        | _ => throwError "hypothesesToCheck contains Actions that are not checker actions"

      -- If there are no calls to other checkers, the body of the sub-checker is trivial
      -- i.e. just `some true`
      if callsToOtherCheckers.isEmpty then
        `($someFn:ident $trueIdent)
      -- If there is just one call to a checker, we inline that checker call
      -- in the body of the sub-checker to avoid the extra indirection
      -- of calling checker combinator functions
      else if callsToOtherCheckers.size == 1 then
        `($(callsToOtherCheckers[0]!))
      -- Otherwise, if there are multiple checker calls,
      -- we produce the code `andOptList [$callsToOtherCheckers,*]`
      else
        `($andOptListFn:ident [$callsToOtherCheckers,*])

    | prodAction :: remainingProdActions =>
      match prodAction with
      | .genInputForInductive fvar hyp _ _ => do
        -- Produces the code `enumeratingOpt (enumST (fun $newVar => $hyp)) (fun $newVar => $continuationBody) initSize`,
        -- which invokes a constrained enumerator that produces values satisfying `hyp` and pass them to `checkerContinuation`
        -- (the continuation handles the remaining producer actions in the tail of the `producerActions` list)
        let newVar := mkIdent $ getUserNameInContext ctor.localCtx fvar
        let hypTerm ← delabExprInLocalContext ctor.localCtx hyp
        let enumSuchThatCall ← `($enumSTFn (fun $newVar:ident => $hypTerm))
        let continuationBody ← mkSubCheckerBody hypothesesToCheck ctor remainingProdActions
        `($enumeratingOptFn:ident $enumSuchThatCall (fun $newVar:ident => $continuationBody) $initSizeIdent)
      | .genFVar fvar _ => do
        -- Produces the code `enumerating enum (fun $newVar => $continuationBody) initSize`
        -- which invokes an unconstrained enumerator that enumerates values of the given type
        -- (the type is determined via typeclass resolution), and passes them to the `continuationBody`
        let newVar := mkIdent $ getUserNameInContext ctor.localCtx fvar
        let continuationBody ← mkSubCheckerBody hypothesesToCheck ctor remainingProdActions
        `($enumeratingFn:ident $enumFn (fun $newVar:ident => $continuationBody) $initSizeIdent)
      | _ => throwError "producerActions contains Actions that are not producer actions"

/-- Constructs an anonymous sub-checker. See the comments in the body of this function
    for details on how this sub-checker is created. -/
def mkSubChecker (subChecker : SubCheckerInfo) : TermElabM (TSyntax `term) := do
  let hypothesesToCheck := Array.toList $
    subChecker.groupedActions.checkNonInductiveActions ++ subChecker.groupedActions.checkInductiveActions
  let producerActions := Array.toList subChecker.groupedActions.gen_list
  let checkerBody ← mkSubCheckerBody hypothesesToCheck subChecker.ctor producerActions

  -- If there are inputs on which we need to perform a pattern-match,
      -- create a pattern-match expr which only returns the checker body
      -- if the match succeeds
  if !subChecker.inputsToMatch.isEmpty then

    -- Handle multiple scrutinees by giving all of them fresh names
    let existingNames := Name.mkStr1 <$> subChecker.inputsToMatch

    -- TODO: rewrite `genFreshName` with local context stuff
    let scrutinees := Array.map (fun paramName =>
      match subChecker.nameMap[paramName]? with
      | some newName => Lean.mkIdent newName
      | none => Lean.mkIdent $ genFreshName existingNames paramName) existingNames

    -- Force delaborator to pretty-print pattern cases in prefix position
    -- (as opposed to using postfix dot-notation, which is not allowed in pattern-matches)
    withOptions setDelaboratorOptions do
      -- Construct the match expression based on the info in `matchCases`
      let mut cases := #[]
      let patterns ← Array.mapM (fun patternExpr => delabExprInLocalContext subChecker.localCtx patternExpr) subChecker.matchCases

      -- If there are multiple scrutinees, the LHS of each case is a tuple containing the elements in `matchCases`
      let case ← `(Term.matchAltExpr| | $[$patterns:term],* => $checkerBody:term)
      cases := cases.push case

      -- The LHS of the catch-all case contains a tuple consisting entirely of wildcards
      let numScrutinees := Array.size scrutinees
      let wildcards := Array.replicate numScrutinees (← `(_))
      let catchAllCase ← `(Term.matchAltExpr| | $wildcards:term,* => $someFn:ident $falseIdent:ident)
      cases := cases.push catchAllCase

      -- Create a pattern match that simultaneously matches on all the scrutinees
      mkSimultaneousMatch scrutinees cases
  else
    return checkerBody

/-- Takes an array of `SubCheckerInfo`s and creates a Lean term representing a
    list of thunked derived sub-checkers -/
def mkThunkedSubCheckers (subCheckerInfos : Array SubCheckerInfo) : TermElabM (TSyntax `term) := do
  let mut thunkedSubCheckers := #[]
  for subChecker in subCheckerInfos do
    let subCheckerBody ← mkSubChecker subChecker
    thunkedSubCheckers := thunkedSubCheckers.push (← `(fun _ => $subCheckerBody))

  `([$thunkedSubCheckers,*])
