import Lean
import Plausible.IR.Constructor
import Plausible.New.Idents


open Plausible.IR
open Lean Elab Command Meta Term Parser Std
open Idents

/-- Produces a trivial generator (e.g. `pure Leaf`)
    when all fields of a `ActionGroup` struct are empty except `ret_list` -/
def mkTrivialGenerator (actionGroup : ActionGroup) : MetaM (TSyntax `term) := do
  let blah := actionGroup.gen_list ++ actionGroup.iflet_list ++ actionGroup.check_IR_list ++ actionGroup.check_nonIR_list
  if not blah.isEmpty then
    `([])
  else
    let mut generators := #[]
    for Action in actionGroup.ret_list do
        if let .ret expr := Action then
        let argToGenTerm ← PrettyPrinter.delab expr
        let generatorBody ← `(fun _ => $pureIdent $argToGenTerm)
        let thunkedGenerator ← `((1, $thunkGenFn ($generatorBody)))
        generators := generators.push thunkedGenerator

    -- Convert the list of generator terms into a Lean list containing all the generators
    `([$generators,*])

-- TODO: implement variant of `mkGeneratorFunction` that takes as its argument an `Array` of `SubGeneratorInfo`s
