import Plausible.IR.Example

import Plausible.Gen
import Plausible.Sampleable
open Plausible

/-- A handwritten generator for BSTs à la "Generating Good Generators for Inductive Relations"
   - We use the `OptionT` monad to add the possibility of failure to the `Gen` monad -/
def genBST (in1 : Nat) (in2 : Nat) : Nat → OptionT Gen Tree :=
  let rec aux_arb (size : Nat) (in1 : Nat) (in2 : Nat) : OptionT Gen Tree :=
    match size with
    | .zero => pure .Leaf
    | .succ size' =>
      (do
        let x ← Gen.choose Nat 0 in2 (by omega)
        if x > in1 then
          let l ← aux_arb size' in1 x
          let r ← aux_arb size' x in2
          pure (.Node x l r)
        else OptionT.fail ) <|> pure .Leaf
  fun size => aux_arb size in1 in2

-- To sample from the generator, we have to do `OptionT.run` to extract the underlying generator,
-- then invoke `Gen.run` to display the generated value in the IO monad
def size := 5

#eval Gen.run (OptionT.run (genBST 1 10 size)) size
