import Lean
import Plausible.GeneratingGoodGenerators.UnificationMonad

open Lean
---------------------------------------------------------------------------------------------
-- Implements figure 4 from "Generating Good Generators for Inductive Relations", POPL '18
--------------------------------------------------------------------------------------------

def foo (inputNamesAndTypes : Array (Name × Expr)) (outputName : Name) (outputType : Expr) : ConstraintMap := sorry
