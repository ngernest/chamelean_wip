import Lean
import Plausible.IR.Prelude
import Plausible.New.DeriveGenerator

open Lean Elab Command Meta Term Parser
open Plausible.IR

----------------------------------------------------------------------
-- Command elaborator for deriving checkers
-----------------------------------------------------------------------

syntax (name := derive_checker) "#derive_checker" "(" term ")" : command

/-- Command elaborator that produces the function header for the checker -/
@[command_elab derive_checker]
def elabDeriveChecker : CommandElab := fun stx => do
  match stx with
  | `(#derive_checker ( $body:term )) => do
    -- Parse the body of the lambda for an application of the inductive relation
    let (inductiveName, args) ← deconstructInductiveApplication body

    logInfo m!"inductiveName = {inductiveName}, args = {args}"

    -- Elaborate the name of the inductive relation and the type
    -- of the value to be generated
    let inductiveExpr ← liftTermElabM $ elabTerm inductiveName none

    let argNameStrings := convertIdentsToStrings args

    -- Create an auxiliary `SubGeneratorInfo` structure that
    -- stores the metadata for each derived sub-generator
    let allSubCheckerInfos ← liftTermElabM $ getSubCheckerInfos inductiveExpr argNameStrings

    -- Every generator is an inductive generator
    -- (they can all be invoked in the inductive case of the top-level generator),
    -- but only certain generators qualify as `BaseGenerator`s
    let _baseCheckerInfo := Array.filter (fun checker => checker.checkerSort == .BaseChecker) allSubCheckerInfos
    let _inductiveCheckerInfo := allSubCheckerInfos





  | _ => throwUnsupportedSyntax
