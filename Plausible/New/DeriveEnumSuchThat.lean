import Lean
import Plausible.New.DeriveConstrainedProducers
import Plausible.New.SubEnumerators

open Plausible.IR
open Lean Elab Command Meta Term Parser Std
open Idents

syntax (name := derive_enumerator) "#derive_enumerator" "(" "fun" "(" ident ":" term ")" "=>" term ")" : command

@[command_elab derive_enumerator]
def elabDeriveEnumerator : CommandElab := fun stx => do
  match stx with
  | `(#derive_enumerator ( fun ( $var:ident : $targetTypeSyntax:term ) => $body:term )) => do

    -- Parse the body of the lambda for an application of the inductive relation
    let (inductiveName, args) ← deconstructInductiveApplication body
    let targetVar := var.getId

    -- Elaborate the name of the inductive relation and the type
    -- of the value to be generated
    let inductiveExpr ← liftTermElabM $ elabTerm inductiveName none

    -- Find the index of the argument in the inductive application for the value we wish to generate
    -- (i.e. find `i` s.t. `args[i] == targetVar`)
    let targetIdxOpt := findTargetVarIndex targetVar args
    if let .none := targetIdxOpt then
      throwError "cannot find index of value to be generated"
    let targetIdx := Option.get! targetIdxOpt

    let argNameStrings := convertIdentsToStrings args

    -- Create an auxiliary `SubGeneratorInfo` structure that
    -- stores the metadata for each derived sub-generator
    let (allSubGeneratorInfos, topLevelLocalCtx, nameMap) ← liftTermElabM $ getSubGeneratorInfos inductiveExpr argNameStrings targetIdx .Enumerator

    -- Every enumerator is an inductive enumerator
    -- (they can all be invoked in the inductive case of the top-level enumerator),
    -- but only certain enumerator qualify as `BaseGenerator`s
    let baseGenInfo := Array.filter (fun gen => gen.generatorSort == .BaseGenerator) allSubGeneratorInfos
    let inductiveGenInfo := allSubGeneratorInfos

    let baseEnumerators ← liftTermElabM $ mkSubEnumeratorList baseGenInfo .BaseGenerator
    let inductiveEnumerators ← liftTermElabM $ mkSubEnumeratorList inductiveGenInfo .InductiveGenerator

    -- Create an instance of the `EnumSuchThat` typeclass
    let typeclassInstance ←
      mkProducerTypeClassInstance baseEnumerators inductiveEnumerators inductiveName
        args targetVar targetTypeSyntax .Enumerator topLevelLocalCtx nameMap

    -- Pretty-print the derived enumerator
    let genFormat ← liftCoreM (PrettyPrinter.ppCommand typeclassInstance)

    -- Display the code for the derived enumerator to the user
    -- & prompt the user to accept it in the VS Code side panel
    liftTermElabM $ Tactic.TryThis.addSuggestion stx
      (Format.pretty genFormat) (header := "Try this enumerator: ")

    -- Elaborate the typeclass instance and add it to the local context
    elabCommand typeclassInstance

  | _ => throwUnsupportedSyntax
