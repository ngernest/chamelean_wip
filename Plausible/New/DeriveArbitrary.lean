import Lean
import Plausible.New.Idents
import Plausible.New.Arbitrary

open Lean Elab Command Meta Term Parser
open Idents

instance : ToMessageData ConstructorVal where
  toMessageData ctorVal :=
    let fields := [
      m!"name := {ctorVal.name}",
      m!"levelParams := {ctorVal.levelParams}",
      m!"type := {ctorVal.type}",
      m!"induct := {ctorVal.induct}",
      m!"cidx := {ctorVal.cidx}",
      m!"numParams := {ctorVal.numParams}",
      m!"numFields := {ctorVal.numFields}",
      m!"isUnsafe := {ctorVal.isUnsafe}"
    ]
    .bracket "{" (.ofList fields) "}"


syntax (name := derive_arbitrary) "#derive_arbitrary" ident : command

/-- Derives an instance of the `ArbitrarySized` typeclass -/
@[command_elab derive_arbitrary]
def elabDeriveArbitrary : CommandElab := fun stx => do
  match stx with
  | `(#derive_arbitrary $typeIdent:ident) => do
    let typeName := typeIdent.getId

    let isInductiveType ← isInductive typeName
    if isInductiveType then
      let inductiveVal ← getConstInfoInduct typeName

      for ctorName in inductiveVal.ctors do
        let ctorVal ← getConstInfoCtor ctorName
        logInfo m!"ctorVal = {ctorVal}"

      let ctorIdent := mkIdent inductiveVal.ctors[0]!

      -- TODO: figure out what to do here
      -- TODO: just use the first sub-generator branch as the default case for `GeneratorCombinators.frequency`

      let typeclassInstance ←
        `(instance : $(mkIdent ``ArbitrarySized) $(mkIdent typeName) where
            $arbitrarySizedIdent:ident := fun _ => $pureIdent $ctorIdent)

      -- Pretty-print the derived generator
      let genFormat ← liftCoreM (PrettyPrinter.ppCommand typeclassInstance)

      -- Display the code for the derived typeclass instance to the user
      -- & prompt the user to accept it in the VS Code side panel
      liftTermElabM $ Tactic.TryThis.addSuggestion stx
        (Format.pretty genFormat) (header := "Try this generator: ")

      elabCommand typeclassInstance

  | _ => throwUnsupportedSyntax
