import Lean
import Plausible.New.Tests

open Lean Elab Command Meta Term Parser

/-- Uses the name of the inductive relation to produce the checker's name -/
def makeCheckerName (inductiveName : Name) : Name :=
  Name.mkStr1 s!"check_{inductiveName}"


----------------------------------------------------------------------
-- Command elaborator for producing the function header for checkers
-----------------------------------------------------------------------

syntax (name := mk_checker_header) "#mk_checker_header " term : command

/-- Command elaborator that produces the function header for the checker -/
@[command_elab mk_checker_header]
def elabMkCheckerHeader : CommandElab := fun stx => do
  match stx with
  | `(#mk_checker_header ( $inductiveApp:term )) =>
    logInfo s!"Collected: {inductiveApp}"

    -- Parse the names of inductive relation + its arguments
    let (inductiveName, args) ← parseInductiveApp inductiveApp

    if !(← isInductive inductiveName) then
      throwErrorAt stx "{inductiveName} is not an inductive, expected an inductive relation"

    -- Associate each argument with an appropriate type expression
    let paramInfo ← analyzeInductiveArgs inductiveName args

    -- Compute the name for the checker function
    let checkerName := makeCheckerName inductiveName
    let checkerIdent := mkIdent checkerName

    -- Extract parameter names and types from the arguments
    let mut params := #[]

    -- Produce size arguments for the checker
    let sizeParam ← `(bracketedBinder| (size : Nat))
    let topSizeParam ← `(bracketedBinder| (top_size : Nat))
    params := params.push sizeParam
    params := params.push topSizeParam

    -- Process each argument from the inductive application
    for (paramName, paramType) in paramInfo do
      let paramIdent := mkIdent paramName
      let param ← `(bracketedBinder| ($paramIdent : $paramType))
      params := params.push param

    let funHeader : TSyntax `command ←
      `(def $checkerIdent $params* : Option Bool :=
        match size with
        | .zero => none
        | .succ size' => none)

    let headerFormat ← liftCoreM (PrettyPrinter.ppCommand funHeader)
    logInfo m!"Generated function header:\n{headerFormat}"

    elabCommand funHeader

  | _ => throwUnsupportedSyntax

-----------
-- Testing
-----------

#mk_checker_header (bst lo hi t)
