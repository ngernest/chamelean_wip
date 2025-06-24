import Lean
import Plausible.IR.Prelude
import Plausible.New.Idents
import Plausible.New.TSyntaxCombinators
import Plausible.New.Arbitrary
import Plausible.New.Utils

open Lean Elab Command Meta Term Parser
open Plausible.IR Idents

/-- `ToMessageData` instance for pretty-printing `ConstructorVal`s -/
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

/-- Takes the name of a constructor for an algebraic data type and returns an array
    containing `(argument_name, argument_type)` pairs  -/
def getCtorArgsNamesAndTypes (ctorName : Name) : MetaM (Array (Name × Expr)) := do
  let ctorInfo ← getConstInfoCtor ctorName

  forallTelescopeReducing ctorInfo.type fun args _ => do
    let mut argNamesAndTypes := #[]
    for arg in args.toList do
      let localDecl ← arg.fvarId!.getDecl
      argNamesAndTypes := Array.push argNamesAndTypes (localDecl.userName, localDecl.type)

    -- Delete the final element of `decomposedCtorType` to obtain
    -- an array containing only the argument types
    -- argNamesAndTypes := Array.pop argNamesAndTypes

    return argNamesAndTypes


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

      let mut nonRecursiveGenerators : TSyntaxArray `term := #[]
      for ctorName in inductiveVal.ctors do
        let ctorIdent := mkIdent ctorName

        let ctorArgNamesTypes ← liftTermElabM $ getCtorArgsNamesAndTypes ctorName

        logInfo m!"ctor {ctorName} has args {ctorArgNamesTypes}"

        let ctorIsRecursive ← liftTermElabM $ isConstructorRecursive typeName ctorName
        if !ctorIsRecursive then
          -- Produce non-recursive generators (these correspond to non-recursive constructors)
          if ctorArgNamesTypes.isEmpty then
            -- Constructor is nullary, we can just use a generator of the form `pure ...`
            let pureGen ← `($pureIdent $ctorIdent)
            nonRecursiveGenerators := nonRecursiveGenerators.push pureGen
          else
            -- TODO: Call `arbitrary` for each of the arguments
            sorry
        else
          -- TODO: figure out how to handle recursive constructors
          sorry

      -- TODO: find a more intelligent way of determining the default generator
      -- ^^ just use the first sub-generator branch as the default case for `GeneratorCombinators.frequency`
      let ctorIdent := mkIdent inductiveVal.ctors[0]!
      let defaultGenerator ← `($pureIdent $ctorIdent)

      -- TODO: figure out how to handle generators for non-trivial constructors

      -- Fetch the ambient local context, which we need to produce user-accessible fresh names
      let localCtx ← liftTermElabM $ getLCtx

      -- Produce a fresh name for the `size` argument for the lambda
      -- at the end of the generator function, as well as the `aux_arb` inner helper function
      let freshSizeIdent := mkFreshAccessibleIdent localCtx `size
      let freshSize' := mkFreshAccessibleIdent localCtx `size'
      let auxArbIdent := mkFreshAccessibleIdent localCtx `aux_arb
      let generatorType ← `($genIdent $typeIdent)

      -- Create the cases for the pattern-match on the size argument
      -- TODO: fill in the list of generators that is supplied to `frequency`
      let mut caseExprs := #[]
      let zeroCase ← `(Term.matchAltExpr| | $(mkIdent ``Nat.zero) => $frequencyFn $defaultGenerator [])
      caseExprs := caseExprs.push zeroCase

      let succCase ← `(Term.matchAltExpr| | $(mkIdent ``Nat.succ) $freshSize' => $frequencyFn $defaultGenerator [])
      caseExprs := caseExprs.push succCase

      -- Create function argument for the generator size
      let sizeParam ← `(Term.letIdBinder| ($sizeIdent : $natIdent))
      let matchExpr ← liftTermElabM $ mkMatchExpr sizeIdent caseExprs

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
