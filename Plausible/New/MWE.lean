import Lean
open Lean Elab Command Meta Term Parser


/-- Constructs a Lean monadic `do` block out of an array of `doSeq`s
    (expressions that appear in the `do` block) -/
def mkDoBlock (doBlockExprs : TSyntaxArray ``Term.doSeq) : MetaM (TSyntax `term) := do
  let doSeqElems := TSyntaxArray.mk doBlockExprs
  let doBlockBody ← `(doSeq| $doSeqElems*)
  `(do $doBlockBody)

/-- `mkLetBind lhs rhsTerms` constructs a monadic let-bind expression of the form
    `let lhs ← e0 e1 … en`, where `rhsTerms := #[e0, e1, …, en]`.
    - Note: `rhsTerms` cannot be empty, otherwise this function throws an exception -/
def mkLetBind (lhs : Ident) (rhsTerms : TSyntaxArray `term) : MetaM (TSyntax ``Term.doSeq) := do
  let rhsList := rhsTerms.toList
  match rhsList with
  | f :: args =>
    let argTerms := args.toArray
    `(doSeq| let $lhs:term ← $f:term $argTerms* )
  | [] => throwError "rhsTerms can't be empty"

-- Dummy function for example purposes
def dummyMonadicFunc (n : Nat) : Option Nat := pure (n + 1)

-- Print the raw expr when the command elaborator below fails
set_option pp.rawOnError true

-- Example command elaborator that triggers the issue
elab "#test_doblock" : command => do
  let mut doBlockExprs := #[]

  -- Create first let-bind: let x ← dummyMonadicFunc 1
  let lhs1 := mkIdent $ Name.mkStr1 "x"
  let rhsTerms1 := #[← `(dummyMonadicFunc), ← `(1)]
  let bind1 ← liftTermElabM $ mkLetBind lhs1 rhsTerms1
  doBlockExprs := doBlockExprs.push bind1

  -- Create second let-bind: let y ← dummyMonadicFunc 2
  let lhs2 := mkIdent $ Name.mkStr1 "y"
  let rhsTerms2 := #[← `(dummyMonadicFunc), ← `(2)]
  let bind2 ← liftTermElabM $ mkLetBind lhs2 rhsTerms2
  doBlockExprs := doBlockExprs.push bind2

  -- Creates the offending do-block
  -- This causes the exception `parenthesize: uncaught backtrack exception`
  let doBlock ← liftTermElabM $ mkDoBlock doBlockExprs
  logInfo m!"{doBlock}"

#test_doblock
