import Lean
import Plausible.Gen
open Lean Meta

-- Create idents for commonly-called functions & commonly-referenced types

namespace Idents

def thunkGenFn : Ident :=
  mkIdent $ Name.mkStr2 "OptionTGen" "thunkGen"
def backtrackFn : Ident :=
  mkIdent $ Name.mkStr2 "OptionTGen" "backtrack"
def interpSampleFn : Ident :=
  mkIdent $ Name.mkStr3 "Plausible" "SampleableExt" "interpSample"

def failFn : Ident := mkIdent $ Name.mkStr2 "OptionT" "fail"
def natIdent : Ident := mkIdent ``Nat
def optionTIdent : Ident := mkIdent ``OptionT
def genIdent : Ident := mkIdent ``Plausible.Gen

end Idents
