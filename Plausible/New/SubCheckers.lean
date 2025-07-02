import Lean
import Plausible.IR.Constructor
import Plausible.IR.Extractor
import Plausible.New.Idents
import Plausible.New.TSyntaxCombinators

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

/-- `mkAuxiliaryCheckerCall hyp checkerStyle` creates a Lean term representing a call to a
    checker that determines whether the hypothesis `hyp` holds (note that `hyp` should be fully applied)
    - The `checkerStyle` argument is used to determine the style in which the checker call should be performed
    - If `checkerStyle = .RecursiveCall`, we produce the term
    `aux_dec initSize size' (<hyp>)`, i.e. we perform a recursive call to the parent `aux_dec` function
    - If `checkerStyle = .TypeClassResolution`, we produce the term
    `DecOpt.decOpt (<hyp>) initSize`, i.e. we  use typeclass resolution to invoke the checker from the typeclass function
    `DecOpt.decOpt` which determines whether `hyp` holds -/
def mkAuxiliaryCheckerCall (hyp : Expr) (checkerStyle : CheckerStyle) : TermElabM (TSyntax `term) := do
  let hypTerm ← PrettyPrinter.delab hyp
  match checkerStyle with
  | .RecursiveCall => `($auxDecFn $initSizeIdent $(mkIdent `size') $hypTerm)
  | .TypeClassResolution => `($decOptFn ($hypTerm) $initSizeIdent)

/-- Constructs terms which constitute calls to checkers corresponding
    to the hypotheses in `inductiveHypothesesToCheck`
    (these are either recursive calls to the current checker function, or invocations of
    the `DecOpt` typeclass instance for the hypotheses)
    - The `ctor` argument is the constructor of the inductive relation corresponding to
      the sub-checker being built -/
def mkSubCheckerBody (inductiveHypothesesToCheck : Array Action) (ctor : InductiveConstructor) : TermElabM (TSyntax `term) :=
  if inductiveHypothesesToCheck.isEmpty then
    `($someFn:ident $trueIdent:ident)
  else do
    let mut callsToOtherCheckers := #[]
    for hypothesis in inductiveHypothesesToCheck do
      match hypothesis with
      | .checkInductive hyp | .checkNonInductive hyp =>
        -- Check if the hypothesis mentions the current inductive relation
        -- If yes, perform a recursive call to the parent checker
        -- Otherwise, perform typeclass resolution & invoke the checker provided by the `DecOpt` instance for the proposition
        let checkerStyle := if hypothesisRecursivelyCallsCurrentInductive hyp ctor then .RecursiveCall else .TypeClassResolution
        let checkerCall ← mkAuxiliaryCheckerCall hyp checkerStyle
        callsToOtherCheckers := callsToOtherCheckers.push checkerCall
      | .(_) => throwError "Unreachable pattern match"

    `($andOptListFn:ident [$callsToOtherCheckers,*])

/-- Constructs an anonymous sub-checker. See the comments in the body of this function
    for details on how this sub-checker is created. -/
def mkSubChecker (subChecker : SubCheckerInfo) : TermElabM (TSyntax `term) := do
  -- TODO: we only need to iterate through check_IR & check_non_IR

  logInfo m!"subChecker = {subChecker}"

  let hypothesesToCheck := subChecker.groupedActions.checkNonInductiveActions ++ subChecker.groupedActions.checkInductiveActions
  let checkerBody ← mkSubCheckerBody hypothesesToCheck subChecker.ctor

  -- If there are inputs on which we need to perform a pattern-match,
      -- create a pattern-match expr which only returns the checker body
      -- if the match succeeds
  if !subChecker.inputsToMatch.isEmpty then
    let mut cases := #[]

    -- Handle multiple scrutinees by giving all of them fresh names
    let existingNames := Name.mkStr1 <$> subChecker.inputsToMatch
    let scrutinees := Lean.mkIdent <$> Array.map (fun name => genFreshName existingNames name) existingNames

    -- Construct the match expression based on the info in `matchCases`
    let patterns ← Array.mapM (fun patternExpr => PrettyPrinter.delab patternExpr) subChecker.matchCases
    -- If there are multiple scrutinees, the LHS of each case is a tuple containing the elements in `matchCases`
    let case ← `(Term.matchAltExpr| | $[$patterns:term],* => $checkerBody:term)
    cases := cases.push case

    -- The LHS of the catch-all case contains a tuple consisting entirely of wildcards
    let numScrutinees := Array.size scrutinees
    let wildcards := Array.replicate numScrutinees (← `(_))
    let catchAllCase ← `(Term.matchAltExpr| | $wildcards:term,* => $someFn:ident $falseIdent:ident)
    cases := cases.push catchAllCase

    -- Create a pattern match that simultaneously matches on all the scrutinees
    let foo ← mkSimultaneousMatch scrutinees cases
    logInfo m!"{foo}"
    return foo
  else
    return checkerBody
