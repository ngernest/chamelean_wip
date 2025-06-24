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
  | `(#derive_arbitrary $targetTypeIdent:ident) => do
    let targetTypeName := targetTypeIdent.getId

    let isInductiveType ← isInductive targetTypeName
    if isInductiveType then
      let inductiveVal ← getConstInfoInduct targetTypeName

      -- Fetch the ambient local context, which we need to produce user-accessible fresh names
      let localCtx ← liftTermElabM $ getLCtx

      -- Produce a fresh name for the `size` argument for the lambda
      -- at the end of the generator function, as well as the `aux_arb` inner helper function
      let freshSizeIdent := mkFreshAccessibleIdent localCtx `size
      let freshSize' := mkFreshAccessibleIdent localCtx `size'
      let auxArbIdent := mkFreshAccessibleIdent localCtx `aux_arb

      let mut nonRecursiveGenerators := #[]
      let mut recursiveGenerators := #[]
      for ctorName in inductiveVal.ctors do
        let ctorIdent := mkIdent ctorName

        let ctorArgNamesTypes ← liftTermElabM $ getCtorArgsNamesAndTypes ctorName

        logInfo m!"ctor {ctorName} has args {ctorArgNamesTypes}"

        let ctorIsRecursive ← liftTermElabM $ isConstructorRecursive targetTypeName ctorName
        -- Produce non-recursive generators (these correspond to non-recursive constructors)
        if ctorArgNamesTypes.isEmpty then
          -- Constructor is nullary, we can just use a generator of the form `pure ...`
          let pureGen ← `($pureIdent $ctorIdent)
          nonRecursiveGenerators := nonRecursiveGenerators.push pureGen
        else
          -- Produce a fresh name for each of the args to the constructor
          let ctorArgNames := Prod.fst <$> ctorArgNamesTypes
          let freshArgIdents := Lean.mkIdent <$> genFreshNames (existingNames := ctorArgNames) (namePrefixes := ctorArgNames)
          let mut doElems := #[]
          if !ctorIsRecursive then
            -- Call `arbitrary` to generate a random value for each of the arguments
            for freshIdent in freshArgIdents do
              let bindExpr ← liftTermElabM $ mkLetBind freshIdent #[arbitraryFn]
              doElems := doElems.push bindExpr

            -- Create an expression `return C x1 ... xn` at the end of the generator, where
            -- `C` is the constructor name and the `xi` are the genreated values for the args
            let pureExpr ← `(doElem| return $ctorIdent $freshArgIdents*)
            doElems := doElems.push pureExpr

            -- Put the body of the generator together
            let generatorBody ← liftTermElabM $ mkDoBlock doElems
            nonRecursiveGenerators := nonRecursiveGenerators.push generatorBody
          else
            -- For recursive constructors, we need to examine each argument to see which of them require
            -- recursive calls to the generator
            let freshArgIdentsTypes := Array.zip freshArgIdents (Prod.snd <$> ctorArgNamesTypes)
            for (freshIdent, argType) in freshArgIdentsTypes do
              if argType.getAppFn.constName == targetTypeName then
                -- Produce a recursive call to `aux_arb`
                let bindExpr ← liftTermElabM $ mkLetBind freshIdent #[auxArbFn, freshSize']
                doElems := doElems.push bindExpr
              else
                -- Call `arbitrary` to generate a random value
                let bindExpr ← liftTermElabM $ mkLetBind freshIdent #[arbitraryFn]
                doElems := doElems.push bindExpr

            -- Create an expression `return C x1 ... xn` at the end of the generator, where
            -- `C` is the constructor name and the `xi` are the genreated values for the args
            let pureExpr ← `(doElem| return $ctorIdent $freshArgIdents*)
            doElems := doElems.push pureExpr

            -- Put the body of the generator together
            let generatorBody ← liftTermElabM $ mkDoBlock doElems
            recursiveGenerators := recursiveGenerators.push generatorBody

      -- Just use the first non-recursive generator as the default generator
      let defaultGenerator := nonRecursiveGenerators[0]!

      -- TODO: figure out how to handle generators for non-trivial constructors

      let generatorType ← `($genIdent $targetTypeIdent)

      let thunkedNonRecursiveGenerators ←
        Array.mapM (fun generatorBody => `($generatorCombinatorsThunkGenFn (fun _ => $generatorBody))) nonRecursiveGenerators

      let mut weightedThunkedNonRecursiveGens := #[]
      for thunkedGen in thunkedNonRecursiveGenerators do
        let thunkedGen ← `((1, $thunkedGen))
        weightedThunkedNonRecursiveGens := weightedThunkedNonRecursiveGens.push thunkedGen

      let mut weightedThunkedRecursiveGens := #[]
      for recursiveGen in recursiveGenerators do
        let thunkedWeightedGen ← `(($succIdent $freshSize', $generatorCombinatorsThunkGenFn (fun _ => $recursiveGen)))
        weightedThunkedRecursiveGens := weightedThunkedRecursiveGens.push thunkedWeightedGen

      -- Create the cases for the pattern-match on the size argument
      let mut caseExprs := #[]
      let zeroCase ← `(Term.matchAltExpr| | $zeroIdent => $oneOfWithDefaultFn $defaultGenerator [$thunkedNonRecursiveGenerators,*])
      caseExprs := caseExprs.push zeroCase


      let mut allThunkedWeightedGenerators ← `([$weightedThunkedNonRecursiveGens,*, $weightedThunkedRecursiveGens,*])
      let succCase ← `(Term.matchAltExpr| | $succIdent $freshSize' => $frequencyFn $defaultGenerator $allThunkedWeightedGenerators)
      caseExprs := caseExprs.push succCase

      -- Create function argument for the generator size
      let sizeParam ← `(Term.letIdBinder| ($sizeIdent : $natIdent))
      let matchExpr ← liftTermElabM $ mkMatchExpr sizeIdent caseExprs

      let typeclassInstance ←
        `(instance : $arbitrarySizedTypeclass $targetTypeIdent where
            $unqualifiedArbitrarySizedFn:ident :=
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
