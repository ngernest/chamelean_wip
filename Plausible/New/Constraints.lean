import Lean
import Plausible.IR.Constructor

open Plausible.IR
open Lean Elab Command Meta Term Parser Std

-- TODO: figure out how to produce a trivial generator (e.g. `pure Leaf`)
-- when all fields of a `GenCheckCall` struct are empty except `ret_list`
-- This will involve porting over some of the existing code
-- from the `getGeneratorForTarget` function in `DeriveGenerator.lean`
