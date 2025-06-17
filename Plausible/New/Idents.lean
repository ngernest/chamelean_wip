import Lean
import Plausible.Gen
open Lean Meta

-- Create idents for commonly-called functions & commonly-referenced types

namespace Idents

def thunkGenFn : Ident := mkIdent $ Name.mkStr2 "OptionTGen" "thunkGen"
def backtrackFn : Ident := mkIdent $ Name.mkStr2 "OptionTGen" "backtrack"
def interpSampleFn : Ident := mkIdent $ Name.mkStr3 "Plausible" "SampleableExt" "interpSample"
def auxArbFn : Ident := mkIdent $ Name.mkStr1 "aux_arb"

def genSizedSuchThatTypeclass : Ident := mkIdent $ Name.mkStr1 "GenSizedSuchThat"
def genSizedSTIdent : Ident := mkIdent $ Name.mkStr1 "genSizedST"

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

end Idents
