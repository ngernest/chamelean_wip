import Lean
import Plausible.IR.Constructor
import Plausible.New.Idents


open Plausible.IR
open Lean Elab Command Meta Term Parser Std
open Idents

/-- Produces a trivial generator (e.g. `pure Leaf`)
    when all fields of a `GenCheckCallGroup` struct are empty except `ret_list` -/
def mkTrivialGenerator (gccGroup : GenCheckCallGroup) : MetaM (TSyntax `term) := do
  let blah := gccGroup.gen_list ++ gccGroup.iflet_list ++ gccGroup.check_IR_list ++ gccGroup.check_nonIR_list
  if not blah.isEmpty then
    `([])
  else
    let mut generators := #[]
    for genCheckCall in gccGroup.ret_list do
        if let .ret expr := genCheckCall then
        let argToGenTerm ← PrettyPrinter.delab expr
        let generatorBody ← `(fun _ => $pureIdent $argToGenTerm)
        let thunkedGenerator ← `((1, $thunkGenFn ($generatorBody)))
        generators := generators.push thunkedGenerator

    -- Convert the list of generator terms into a Lean list containing all the generators
    `([$generators,*])
