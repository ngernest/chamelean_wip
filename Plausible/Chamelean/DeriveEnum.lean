import Lean

import Plausible.Chamelean.Idents
import Plausible.Chamelean.TSyntaxCombinators
import Plausible.Chamelean.Enumerators
import Plausible.Chamelean.Utils
import Plausible.Chamelean.DeriveArbitrary

open Lean Elab Command Meta Term Parser

open Idents

/-- Creates an instance of the `ArbitrarySized` typeclass for an inductive type
    whose name is given by `targetTypeName`.

    (Note: the main logic for determining the structure of the derived generator
    is contained in this function.) -/
def mkEnumSizedInstance (targetTypeName : Name) : CommandElabM (TSyntax `command) := do
  -- Obtain Lean's `InductiveVal` data structure, which contains metadata about
  -- the type corresponding to `targetTypeName`
  let inductiveVal ← getConstInfoInduct targetTypeName

  -- Fetch the ambient local context, which we need to produce user-accessible fresh names
  let localCtx ← liftTermElabM $ getLCtx

  -- Produce a fresh name for the `size` argument for the lambda
  -- at the end of the generator function, as well as the `aux_arb` inner helper function
  let freshSizeIdent := mkFreshAccessibleIdent localCtx `size
  let freshSize' := mkFreshAccessibleIdent localCtx `size'

  let mut nonRecursiveEnumerators := #[]
  let mut recursiveEnumerators := #[]
  for ctorName in inductiveVal.ctors do
    let ctorIdent := mkIdent ctorName

    let ctorArgNamesTypes ← liftTermElabM $ getCtorArgsNamesAndTypes ctorName

    if ctorArgNamesTypes.isEmpty then
      -- Constructor is nullary, we can just use an enumerator of the form `pure ...`
      let pureGen ← `($pureFn $ctorIdent)
      nonRecursiveEnumerators := nonRecursiveEnumerators.push pureGen
    else
      -- Produce a fresh name for each of the args to the constructor
      let ctorArgNames := Prod.fst <$> ctorArgNamesTypes
      let freshArgIdents := Lean.mkIdent <$> genFreshNames (existingNames := ctorArgNames) (namePrefixes := ctorArgNames)

      let mut doElems := #[]

      -- Determine whether the constructor has any recursive arguments
      let ctorIsRecursive ← liftTermElabM $ isConstructorRecursive targetTypeName ctorName
      if !ctorIsRecursive then
        -- Call `enum` to enumerate a random value for each of the arguments
        for freshIdent in freshArgIdents do
          let bindExpr ← liftTermElabM $ mkLetBind freshIdent #[enumFn]
          doElems := doElems.push bindExpr
      else
        -- For recursive constructors, we need to examine each argument to see which of them require
        -- recursive calls to the generator
        let freshArgIdentsTypes := Array.zip freshArgIdents (Prod.snd <$> ctorArgNamesTypes)
        for (freshIdent, argType) in freshArgIdentsTypes do
          -- If the argument's type is the same as the target type,
          -- produce a recursive call to the enumerator using `aux_enum`,
          -- otherwise enumerate a value using `enum`
          let bindExpr ←
            liftTermElabM $
              if argType.getAppFn.constName == targetTypeName then
                mkLetBind freshIdent #[auxEnumFn, freshSize']
              else
                mkLetBind freshIdent #[enumFn]
          doElems := doElems.push bindExpr

      -- Create an expression `return C x1 ... xn` at the end of the generator, where
      -- `C` is the constructor name and the `xi` are the generated values for the args
      let pureExpr ← `(doElem| return $ctorIdent $freshArgIdents*)
      doElems := doElems.push pureExpr

      -- Put the body of the enumerator together
      let enumeratorBody ← liftTermElabM $ mkDoBlock doElems
      if !ctorIsRecursive then
        nonRecursiveEnumerators := nonRecursiveEnumerators.push enumeratorBody
      else
        recursiveEnumerators := recursiveEnumerators.push enumeratorBody

  -- Just use the first non-recursive enumerator as the default enumerator
  let defaultGenerator := nonRecursiveEnumerators[0]!


  -- Create the cases for the pattern-match on the size argument
  -- If `size = 0`, pick one of the thunked non-recursive generators
  let mut caseExprs := #[]
  let zeroCase ← `(Term.matchAltExpr| | $zeroIdent => $oneOfWithDefaultEnumCombinatorFn $defaultGenerator [$nonRecursiveEnumerators,*])
  caseExprs := caseExprs.push zeroCase

  -- If `size = .succ size'`, pick an enumerator (it can be non-recursive or recursive)
  let mut allEnumerators ← `([$nonRecursiveEnumerators,*, $recursiveEnumerators,*])
  let succCase ← `(Term.matchAltExpr| | $succIdent $freshSize' => $oneOfWithDefaultEnumCombinatorFn $defaultGenerator $allEnumerators)
  caseExprs := caseExprs.push succCase

  -- Create function argument for the enumerator size
  let sizeParam ← `(Term.letIdBinder| ($sizeIdent : $natIdent))
  let matchExpr ← liftTermElabM $ mkMatchExpr sizeIdent caseExprs

  -- Create an instance of the `EnumSized` typeclass
  let targetTypeIdent := mkIdent targetTypeName
  let enumeratorType ← `($enumTypeConstructor $targetTypeIdent)
  `(instance : $enumSizedTypeclass $targetTypeIdent where
      $unqualifiedEnumSizedFn:ident :=
        let rec $auxEnumFn:ident $sizeParam : $enumeratorType :=
          $matchExpr
      fun $freshSizeIdent => $auxEnumFn $freshSizeIdent)

syntax (name := derive_enum) "#derive_enum" term : command

/-- Command elaborator which derives an instance of the `EnumSized` typeclass -/
@[command_elab derive_enum]
def elabDeriveEnum : CommandElab := fun stx => do
  match stx with
  | `(#derive_enum $targetTypeTerm:term) => do

    -- TODO: figure out how to support parameterized types
    let targetTypeIdent ←
      match targetTypeTerm with
      | `($tyIdent:ident) => pure tyIdent
      | _ => throwErrorAt targetTypeTerm "Parameterized types not supported"
    let targetTypeName := targetTypeIdent.getId

    let isInductiveType ← isInductive targetTypeName
    if isInductiveType then
      let typeClassInstance ← mkEnumSizedInstance targetTypeName

      -- Pretty-print the derived enumerator
      let enumFormat ← liftCoreM (PrettyPrinter.ppCommand typeClassInstance)

      -- Display the code for the derived typeclass instance to the user
      -- & prompt the user to accept it in the VS Code side panel
      liftTermElabM $ Tactic.TryThis.addSuggestion stx
        (Format.pretty enumFormat) (header := "Try this enumerator: ")

      -- Elaborate the typeclass instance and add it to the local context
      elabCommand typeClassInstance
    else
      throwError "Cannot derive Enum instance for non-inductive types"

  | _ => throwUnsupportedSyntax

/-- Deriving handler which produces an instance of the `EnumSized` typeclass for
    each type specified in `declNames` -/
def deriveEnumInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive) then
    for targetTypeName in declNames do
      let typeClassInstance ← mkEnumSizedInstance targetTypeName
      elabCommand typeClassInstance
    return true
  else
    throwError "Cannot derive instance of Enum typeclass for non-inductive types"
    return false

initialize
  registerDerivingHandler ``Enum deriveEnumInstanceHandler
