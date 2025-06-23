import Lean
import Plausible.Gen
open Lean Meta

-- Create idents for commonly-called functions & commonly-referenced types

namespace Idents

def thunkGenFn : Ident := mkIdent $ Name.mkStr2 "OptionTGen" "thunkGen"
def backtrackFn : Ident := mkIdent $ Name.mkStr2 "OptionTGen" "backtrack"
def frequencyFn : Ident := mkIdent $ Name.mkStr2 "GeneratorCombinators" "frequency"
def interpSampleFn : Ident := mkIdent $ Name.mkStr3 "Plausible" "SampleableExt" "interpSample"
def auxArbFn : Ident := mkIdent $ Name.mkStr1 "aux_arb"

def ArbitrarySizedSuchThatTypeclass : Ident := mkIdent $ Name.mkStr1 "ArbitrarySizedSuchThat"
def arbitrarySizedTypeclass : Ident := mkIdent $ Name.mkStr1 "ArbitrarySized"
def arbitrarySizedIdent : Ident := mkIdent $ Name.mkStr1 "arbitrarySized"
def arbitrarySizedSTIdent : Ident := mkIdent $ Name.mkStr1 "arbitrarySizedST"
def qualifiedarbitrarySizedSTIdent : Ident := mkIdent $ Name.mkStr2 "ArbitrarySuchThat" "arbitraryST"
def qualifiedDecOptIdent : Ident := mkIdent $ Name.mkStr2 "DecOpt" "decOpt"

/-- `Ident` representing `OptionT.fail`-/
def failFn : Ident := mkIdent $ Name.mkStr2 "OptionT" "fail"

def natIdent : Ident := mkIdent ``Nat
def optionTIdent : Ident := mkIdent ``OptionT
def genIdent : Ident := mkIdent ``Plausible.Gen
def pureIdent : Ident := mkIdent $ Name.mkStr1 "pure"
def initSizeIdent : Ident := mkIdent $ Name.mkStr1 "initSize"
def sizeIdent : Ident := mkIdent $ Name.mkStr1 "size"

/-- Produces a fresh user-facing & *accessible* identifier with respect to the local context
    - Note: prefer using this function over `Core.mkFreshUserName`, which is meant
      to create fresh names that are *inaccessible* to the user (i.e. `mkFreshUserName` will
      add daggers (`†`) to the name to make them inaccessible).
    - This function ensures that the identifier is fresh
      by adding suffixes containing underscores/numbers when necessary (in lieu of adding daggers). -/
def mkFreshAccessibleIdent (localCtx : LocalContext) (name : Name) : Ident :=
  mkIdent $ LocalContext.getUnusedName localCtx name

/-- `genFreshName existingNames namePrefix` produces a thunked function
    that produces a fresh name (with prefix `namePrefix`) that are guaranteed to be
    not within the existing set of names
    - Note: the body of this function operates in the identity monad since
      we want local mutable state and access to the syntactic sugar
      provided by `while` loops -/
def genFreshName (existingNames : Array Name) (namePrefix : Name) : Name :=
  Id.run do
    let mut count := 0
    let mut freshName := Name.appendAfter namePrefix s!"_{count}"
    while (existingNames.contains freshName) do
      count := count + 1
      freshName := Name.appendAfter namePrefix s!"_{count}"
    return freshName

end Idents
