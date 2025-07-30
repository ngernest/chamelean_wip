/-
Copyright (c) 2025 Ernest Ng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ernest Ng
-/
import Lean.Elab
import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util

import Plausible.Idents
import Plausible.TSyntaxCombinators
import Plausible.Arbitrary
import Plausible.Utils

open Lean Elab Meta Parser Term
open Elab.Deriving
open Elab.Command

/-!

# Deriving Handler for `Arbitrary` typeclass

This file defines a handler which automatically derives `Arbitrary` instances
for inductive types.

(Note that the deriving handler technically derives `ArbitraryFueled` instancces,
but every `ArbitraryFueled` instance automatically results in an `Arbitrary` instance,
as detailed in `Arbitrary.lean`.)

Example usage:

```lean
-- Datatype for binary trees
inductive Tree
  | Leaf : Tree
  | Node : Nat → Tree → Tree → Tree
  deriving Arbitrary
```

To sample from a derived generator, users can simply call `Arbitrary.runArbitrary`, specify the type
for the desired generated values and provide some Nat to act as the generator's fuel parameter (10 in the example below):

```lean
#eval Arbitrary.runArbitrary (α := Tree) 10
```

To view the code for the derived generator, users can enable trace messages using the `plausible.deriving.arbitrary` trace class as follows:

```lean
set_option trace.plausible.deriving.arbitrary true
```

## Main definitions
* Deriving handler for `ArbitraryFueled` typeclass

-/

namespace Plausible

open Arbitrary

/-- Takes the name of a constructor for an algebraic data type and returns an array
    containing `(argument_name, argument_type)` pairs.

    If the algebraic data type is defined using anonymous constructor argument syntax, i.e.
    ```
    inductive T where
      C1 : τ1 → … → τn
      …
    ```
    Lean produces macro scopes when we try to access the names for the constructor args.
    In this case, we remove the macro scopes so that the name is user-accessible.
    (This will result in constructor argument names being non-unique in the array
    that is returned -- it is the caller's responsibility to produce fresh names,
    e.g. using `Idents.genFreshNames`.)
-/
def getCtorArgsNamesAndTypes (header : Header) (indVal : InductiveVal) (ctorName : Name) : MetaM (Array (Name × Expr)) := do
  let ctorInfo ← getConstInfoCtor ctorName

  forallTelescopeReducing ctorInfo.type fun args _ => do
    let mut argNamesAndTypes := #[]

    for i in *...args.size do
      let arg := args[i]!
      let localDecl ← arg.fvarId!.getDecl
      let argType := localDecl.type

      let argName ← if i < indVal.numParams then pure header.argNames[i]! else Core.mkFreshUserName `a
      if i < indVal.numParams then
        continue
      else
        argNamesAndTypes := argNamesAndTypes.push (argName, argType)

    return argNamesAndTypes

------------------
-- NEW CODE BELOW
------------------

open TSyntax.Compat in
/-- Variant of `Deriving.Util.mkHeader` where we don't add an explicit binder
    of the form `($targetName : $targetType)` to the field `binders`
    (i.e. `binders` contains only implicit binders) -/
def mkHeaderWithOnlyImplicitBinders (className : Name) (arity : Nat) (indVal : InductiveVal) : TermElabM Header := do
  let argNames      ← mkInductArgNames indVal
  let binders       ← mkImplicitBinders argNames
  let targetType    ← mkInductiveApp indVal argNames
  let mut targetNames := #[]
  for _ in [:arity] do
    targetNames := targetNames.push (← mkFreshUserName `x)
  let binders      := binders ++ (← mkInstImplicitBinders className indVal argNames)
  return {
    binders     := binders
    argNames    := argNames
    targetNames := targetNames
    targetType  := targetType
  }

def mkArbitraryHeader (indVal : InductiveVal) : TermElabM Header :=
  mkHeaderWithOnlyImplicitBinders ``ArbitraryFueled 1 indVal

def mkBody (header : Header) (inductiveVal : InductiveVal) (generatorType : TSyntax `term) : TermElabM Term := do
  -- Fetch the name of the target type (the type for which we are deriving a generator)
  let targetTypeName := inductiveVal.name

  -- Fetch the empty local context
  let localCtx ← getLCtx

  -- Produce `Ident`s for the `fuel` argument for the lambda
  -- at the end of the generator function, as well as the `aux_arb` inner helper function
  let freshFuel := mkIdent $ localCtx.getUnusedName `fuel
  let freshFuel' := mkIdent $ localCtx.getUnusedName `fuel'
  let auxArb := mkIdent `aux_arb

  let mut nonRecursiveGenerators := #[]
  let mut recursiveGenerators := #[]
  for ctorName in inductiveVal.ctors do
    let ctorIdent := mkIdent ctorName

    let ctorArgNamesTypes ← getCtorArgsNamesAndTypes header inductiveVal ctorName
    let (ctorArgNames, ctorArgTypes) := Array.unzip ctorArgNamesTypes

    /- Produce fresh names for each of the constructor's arguments.
      Producing fresh names is necessary in order to handle
      constructors expressed using the following syntax:
      ```
      inductive Foo
        | C : T1 → ... → Tn
      ```
      in which all the arguments to the constructor `C` don't have explicit names.

      (Note: we use `genFreshNames` instead of `LocalContext.getUnusedName` here
      to ensure that when there are multiple arguments,
      every single argument gets a fresh name. All of the fresh names are added
      to the `LocalContext` later in this function, ensuring that the `LocalContext`
      remains updated.)
    -/
    let freshArgNames := Idents.genFreshNames (existingNames := ctorArgNames) (namePrefixes := ctorArgNames)
    let freshArgNamesTypes := Array.zip freshArgNames ctorArgTypes
    let freshArgIdents := Lean.mkIdent <$> freshArgNames
    let freshArgIdentsTypes := Array.zip freshArgIdents ctorArgTypes

    if ctorArgNamesTypes.isEmpty then
      -- Constructor is nullary, we can just use a generator of the form `pure ...`
      let pureGen ← `($(Lean.mkIdent `pure) $ctorIdent)
      nonRecursiveGenerators := nonRecursiveGenerators.push pureGen
    else
      -- Add all the freshened names for the constructor to the local context,
      -- then produce the body of the sub-generator
      let (generatorBody, ctorIsRecursive) ←
        withLocalDeclsDND freshArgNamesTypes (fun _ => do
          let mut doElems := #[]

          -- Determine whether the constructor has any recursive arguments
          let ctorIsRecursive ← isConstructorRecursive targetTypeName ctorName
          if !ctorIsRecursive then
            -- Call `arbitrary` to generate a random value for each of the arguments
            for freshIdent in freshArgIdents do
              let bindExpr ← mkLetBind freshIdent #[(mkIdent ``Arbitrary.arbitrary)]
              doElems := doElems.push bindExpr
          else
            -- For recursive constructors, we need to examine each argument to see which of them require
            -- recursive calls to the generator
            for (freshIdent, argType) in freshArgIdentsTypes do
              -- If the argument's type is the same as the target type,
              -- produce a recursive call to the generator using `aux_arb`,
              -- otherwise generate a value using `arbitrary`
              let bindExpr ←
                if argType.getAppFn.constName == targetTypeName then
                  mkLetBind freshIdent #[(mkIdent `aux_arb), freshFuel']
                else
                  mkLetBind freshIdent #[(mkIdent ``Arbitrary.arbitrary)]
              doElems := doElems.push bindExpr

          -- Create an expression `return C x1 ... xn` at the end of the generator, where
          -- `C` is the constructor name and the `xi` are the generated values for the args
          let pureExpr ← `(doElem| return $ctorIdent $freshArgIdents*)
          doElems := doElems.push pureExpr

          -- Put the body of the generator together
          let generatorBody ← mkDoBlock doElems
          pure (generatorBody, ctorIsRecursive))

      if !ctorIsRecursive then
        nonRecursiveGenerators := nonRecursiveGenerators.push generatorBody
      else
        recursiveGenerators := recursiveGenerators.push generatorBody

  -- Use the first non-recursive generator as the default generator
  -- If the target type has no non-recursive constructors, we emit an error message
  -- saying that we cannot derive a generator for that type
  let defaultGenerator ← Option.getDM (nonRecursiveGenerators[0]?)
    (throwError m!"derive Arbitrary failed, {targetTypeName} has no non-recursive constructors")

  -- Explicitly parenthesize the body of each sub-generator for clarity
  let nonRecursiveGens ←
    Array.mapM (fun generatorBody => `( ($generatorBody) )) nonRecursiveGenerators

  -- Turn each generator into a thunked function and associate each generator with its weight
  -- (1 for non-recursive generators, `fuel' + 1` for recursive generators)
  let mut weightedNonRecursiveGenerators := #[]
  for generator in nonRecursiveGenerators do
    let weightedGen ← `((1, ($generator)))
    weightedNonRecursiveGenerators := weightedNonRecursiveGenerators.push weightedGen

  let mut weightedRecursiveGenerators := #[]
  for recursiveGen in recursiveGenerators do
    let thunkedWeightedGen ← ``(($freshFuel' + 1, ($recursiveGen)))
    weightedRecursiveGenerators := weightedRecursiveGenerators.push thunkedWeightedGen

  -- Create the cases for the pattern-match on the fuel argument
  -- If `fuel = 0`, pick one of the thunked non-recursive generators
  let mut caseExprs := #[]
  let zeroCase ← `(Term.matchAltExpr| | $(mkIdent ``Nat.zero) => $(mkIdent ``Gen.oneOfWithDefault) $defaultGenerator [$nonRecursiveGens,*])
  caseExprs := caseExprs.push zeroCase

  -- If `fuel = fuel' + 1`, pick a generator (it can be non-recursive or recursive)
  let mut allWeightedGenerators ← `([$weightedNonRecursiveGenerators,*, $weightedRecursiveGenerators,*])
  let succCase ← `(Term.matchAltExpr| | $freshFuel' + 1 => $(mkIdent ``Gen.frequency) $defaultGenerator $allWeightedGenerators)
  caseExprs := caseExprs.push succCase

  -- Create function argument for the generator fuel
  let fuelParam ← `(Term.letIdBinder| ($freshFuel : $(mkIdent `Nat)))
  let matchExpr ← mkMatchExpr freshFuel caseExprs

  -- Create an instance of the `ArbitraryFueled` typeclass
  `(let rec $auxArb:ident $fuelParam : $generatorType :=
      $matchExpr
    fun $freshFuel => $auxArb $freshFuel)



def mkAuxFunction (ctx : Deriving.Context) (i : Nat) : TermElabM Command := do
  let auxFunName := ctx.auxFunNames[i]!
  let indVal := ctx.typeInfos[i]!
  let header ← mkArbitraryHeader indVal
  let mut binders := header.binders

  let targetType ← mkInductiveApp ctx.typeInfos[i]! header.argNames
  let generatorType ← `($(mkIdent ``Plausible.Gen) $targetType)

  let mut body ← mkBody header indVal generatorType

  `(def $(mkIdent auxFunName):ident $binders:bracketedBinder* : $(mkIdent ``Nat) → $generatorType := $body:term)

def mkMutualBlock (ctx : Deriving.Context) : TermElabM Syntax := do
  let mut auxDefs := #[]
  for i in *...ctx.typeInfos.size do
    auxDefs := auxDefs.push (← mkAuxFunction ctx i)
  `(mutual
     $auxDefs:command*
    end)

private def mkArbitraryInstanceCmd (declName : Name) : TermElabM (Array Syntax) := do
  let ctx ← mkContext "arbitrary" declName
  let cmds := #[← mkMutualBlock ctx] ++ (← mkInstanceCmds ctx ``ArbitraryFueled #[declName])
  trace[plausible.deriving.arbitrary] "\n{cmds}"
  return cmds

/-- Deriving handler which produces an instance of the `ArbitraryFueled` typeclass for
    each type specified in `declNames` -/
def mkArbitraryInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive) then
    for declName in declNames do
      let cmds ← liftTermElabM $ mkArbitraryInstanceCmd declName
      cmds.forM elabCommand
    return true
  else
    throwError "Cannot derive instance of Arbitrary typeclass for non-inductive types"
    return false

initialize
  registerDerivingHandler ``Arbitrary mkArbitraryInstanceHandler

end Plausible
