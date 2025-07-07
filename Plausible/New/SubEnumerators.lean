import Lean
import Plausible.IR.Constructor
import Plausible.New.Idents
import Plausible.New.TSyntaxCombinators
import Plausible.New.SubGenerators

open Plausible.IR
open Lean Elab Command Meta Term Parser Std
open Idents

/-- Creates a list of sub-enumerator terms (to be passed to the `enumerate` enumerator combinator) -/
def mkSubEnumeratorList (subGeneratorInfos : Array SubGeneratorInfo)
  (generatorSort : GeneratorSort) : TermElabM (TSyntax `term) := do

  let mut subEnumerators ← Array.mapM mkSubGenerator subGeneratorInfos

  if let .BaseGenerator := generatorSort then
    subEnumerators := subEnumerators.push (← `($failFn))

  `([$subEnumerators,*])
