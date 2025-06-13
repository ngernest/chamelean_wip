import Lean
import Plausible.New.DoBlocks

open Lean Elab Command Meta Term Parser


-- Dummy monadic function for example purposes
def dummyMonadicFunc (n : Nat) : Option Nat := pure (n * 2)

-- Print the raw expr when the command elaborator below fails
set_option pp.rawOnError true


/- Example command elaborator that triggers the issue:
   In this example, we are trying to create the do-block
  ```
  do
     let x ← dummyMonadicFunc 1
     let y ← dummyMonadicFunc 2
     return (x, y)
  ```
-/
elab "#test_doblock" : command => do
  let mut doBlockExprs := #[]

  -- Creates `let x ← dummyMonadicFunc 1`
  let x := mkIdent $ Name.mkStr1 "x"
  let rhs1 := #[← `(dummyMonadicFunc), ← `(1)]
  let bind1 ← liftTermElabM $ mkLetBind x rhs1
  doBlockExprs := doBlockExprs.push bind1

  -- Creates `let y ← dummyMonadicFunc 2`
  let y := mkIdent $ Name.mkStr1 "y"
  let rhs2 := #[← `(dummyMonadicFunc), ← `(2)]
  let bind2 ← liftTermElabM $ mkLetBind y rhs2
  doBlockExprs := doBlockExprs.push bind2

  -- Creates `return (x, y)`
  let returnExpr ← `(doElem| return ($x, $y))
  doBlockExprs := doBlockExprs.push returnExpr

  -- Creates the offending do-block
  -- This causes the exception `parenthesize: uncaught backtrack exception`
  let doBlock ← liftTermElabM $ mkDoBlock doBlockExprs
  logInfo m!"{doBlock}"

#test_doblock
