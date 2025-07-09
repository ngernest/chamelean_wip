import Lean
import Std
import Plausible.GeneratingGoodGenerators.UnificationMonad

open Lean
---------------------------------------------------------------------------------------------
-- Implements figure 4 from "Generating Good Generators for Inductive Relations", POPL '18
--------------------------------------------------------------------------------------------

/-- Creates the initial constraint map κ where all inputs are `Fixed` and the output is `Undef`
    - Note: we don't handle universally quantified variables `x` for now -/
def mkInitialConstraintMap (inputNames: List Name) (outputName : Name) (outputType : Expr) : ConstraintMap :=
  -- All inputs are fixed
  let inputConstraints := inputNames.zip (List.replicate inputNames.length .Fixed)
  let outputConstraints := [(outputName, .Undef outputType)]
  Std.HashMap.ofList $ inputConstraints ++ outputConstraints
