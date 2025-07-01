import Lean
import Plausible.IR.Constructor
import Plausible.New.Idents
import Plausible.New.TSyntaxCombinators

open Plausible.IR
open Idents
open Lean Elab Command Meta Term Parser Std

def mkSubCheckerBody : Unit → TermElabM (TSyntax `term) :=
  -- TODO: fill in this body
  sorry

/-- Constructs an anonymous sub-checker. See the comments in the body of this function
    for details on how this sub-checker is created. -/
def mkSubChecker (subChecker : SubCheckerInfo) : TermElabM (TSyntax `term) := do
  -- TODO: we only need to iterate through check_IR & check_non_IR

  -- TODO: use `hypothesisRecursivelyCallsCurrentInductive` to determine if
  -- checker call should be recursive or performed via typeclass resolution
  -- let checkerBody ← mkSubCheckerBody ()
  let checkerBody ← `($someFn:ident $falseIdent:ident) -- TODO: replace


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
