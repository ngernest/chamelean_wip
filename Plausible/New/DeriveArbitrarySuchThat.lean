import Lean
import Plausible.New.DeriveConstrainedProducers
import Plausible.New.SubGenerators

open Plausible.IR
open Lean Elab Command Meta Term Parser Std
open Idents

syntax (name := derive_generator) "#derive_generator" "(" "fun" "(" ident ":" term ")" "=>" term ")" : command

@[command_elab derive_generator]
def elabDeriveGenerator : CommandElab := fun stx => do
  match stx with
  | `(#derive_generator ( fun ( $var:ident : $targetTypeSyntax:term ) => $body:term )) => do

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
    let allSubGeneratorInfos ← liftTermElabM $ getSubGeneratorInfos inductiveExpr argNameStrings targetIdx .Generator

    -- Every generator is an inductive generator
    -- (they can all be invoked in the inductive case of the top-level generator),
    -- but only certain generators qualify as `BaseGenerator`s
    let baseGenInfo := Array.filter (fun gen => gen.generatorSort == .BaseGenerator) allSubGeneratorInfos
    let inductiveGenInfo := allSubGeneratorInfos

    let baseGenerators ← liftTermElabM $ mkWeightedThunkedSubGenerators baseGenInfo .BaseGenerator
    let inductiveGenerators ← liftTermElabM $ mkWeightedThunkedSubGenerators inductiveGenInfo .InductiveGenerator

    let typeclassInstance ← mkProducerTypeClassInstance baseGenerators inductiveGenerators inductiveName args targetVar targetTypeSyntax .Generator

    -- Pretty-print the derived generator
    let genFormat ← liftCoreM (PrettyPrinter.ppCommand typeclassInstance)

    -- Display the code for the derived generator to the user
    -- & prompt the user to accept it in the VS Code side panel
    liftTermElabM $ Tactic.TryThis.addSuggestion stx
      (Format.pretty genFormat) (header := "Try this generator: ")

    -- Elaborate the typeclass instance and add it to the local context
    elabCommand typeclassInstance

  | _ => throwUnsupportedSyntax
