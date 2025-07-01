import Lean
import Plausible.IR.Constructor
import Plausible.New.Idents
import Plausible.New.TSyntaxCombinators

open Plausible.IR
open Idents
open Lean Elab Command Meta Term Parser Std

/-- Constructs terms which constitute calls to checkers corresponding
    to the hypotheses in `inductiveHypothesesToCheck`
    (these are either recursive calls to the current checker function, or invocations of
    the `DecOpt` typeclass instance for the hypotheses) -/
def mkSubCheckerBody (inductiveHypothesesToCheck : Array Action) : TermElabM (TSyntax `term) :=
  if inductiveHypothesesToCheck.isEmpty then
    `($someFn:ident $trueIdent:ident)
  else
    -- TODO: fill in the list with sub-checker calls
    -- ^^ loop through `inductiveHypothesesToCheck` and use `hypothesisRecursivelyCallsCurrentInductive` to determine if
    -- checker call should be recursive or performed via typeclass resolution
    `($andOptListFn:ident [])

/-- Constructs an anonymous sub-checker. See the comments in the body of this function
    for details on how this sub-checker is created. -/
def mkSubChecker (subChecker : SubCheckerInfo) : TermElabM (TSyntax `term) := do
  -- TODO: we only need to iterate through check_IR & check_non_IR

  logInfo m!"subChecker = {subChecker}"

  let inductiveHypothesesToCheck := subChecker.groupedActions.checkInductiveActions
  let checkerBody ← mkSubCheckerBody inductiveHypothesesToCheck

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
