import Lean
import Plausible.New.Idents
import Plausible.New.TSyntaxCombinators
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
        -- logInfo m!"ctorVal = {ctorVal}"

      -- TODO: find a more intelligent way of determining the default generator
      -- ^^ just use the first sub-generator branch as the default case for `GeneratorCombinators.frequency`
      let ctorIdent := mkIdent inductiveVal.ctors[0]!
      let defaultGenerator ← `($pureIdent $ctorIdent)

      -- TODO: figure out what to do here

      -- Create the cases for the pattern-match on the size argument
      -- TODO: fill in the list of generators that is supplied to `frequency`
      let mut caseExprs := #[]
      let zeroCase ← `(Term.matchAltExpr| | $(mkIdent ``Nat.zero) => $frequencyFn $defaultGenerator [])
      caseExprs := caseExprs.push zeroCase

      let succCase ← `(Term.matchAltExpr| | $(mkIdent ``Nat.succ) $(mkIdent `size') => $frequencyFn $defaultGenerator [])
      caseExprs := caseExprs.push succCase

      -- Create function argument for the generator size
      let sizeParam ← `(Term.letIdBinder| ($sizeIdent : $natIdent))
      let matchExpr ← liftTermElabM $ mkMatchExpr sizeIdent caseExprs

      -- Fetch the ambient local context, which we need to produce user-accessible fresh names
      let localCtx ← liftTermElabM $ getLCtx

      -- Produce a fresh name for the `size` argument for the lambda
      -- at the end of the generator function
      let freshSizeIdent := mkFreshAccessibleIdent localCtx `size
      let auxArbIdent := mkFreshAccessibleIdent localCtx `aux_arb
      let generatorType ← `($genIdent $typeIdent)

      let typeclassInstance ←
        `(instance : $(mkIdent ``ArbitrarySized) $(mkIdent typeName) where
            $arbitrarySizedIdent:ident :=
              let rec $auxArbIdent:ident $sizeParam : $generatorType :=
                $matchExpr
            fun $freshSizeIdent => $auxArbIdent $freshSizeIdent)

      -- Pretty-print the derived generator
      let genFormat ← liftCoreM (PrettyPrinter.ppCommand typeclassInstance)

      -- Display the code for the derived typeclass instance to the user
      -- & prompt the user to accept it in the VS Code side panel
      liftTermElabM $ Tactic.TryThis.addSuggestion stx
        (Format.pretty genFormat) (header := "Try this generator: ")

      elabCommand typeclassInstance

  | _ => throwUnsupportedSyntax
