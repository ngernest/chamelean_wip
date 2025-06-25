
import Plausible.Gen
import Plausible.New.OptionTGen
import Plausible.New.DecOpt
import Plausible.New.ArbitrarySizedSuchThat
import Plausible.New.DeriveGenerator
import Test.DeriveArbitrarySuchThat.DeriveBSTGenerator

open ArbitrarySizedSuchThat OptionTGen

set_option guard_msgs.diff true

-- Example taken from "Generating Good Generators for Inductive Relations", section 3
inductive GoodTree : Nat → Nat → BinaryTree → Prop where
  | GoodLeaf : ∀ n, GoodTree n n .Leaf

-- TODO: (fix this)
-- we want to invoke `in2_0 = in1_0` in the checker, not `in1 = in1_0`!

/--
info: Try this generator: instance : ArbitrarySizedSuchThat BinaryTree (fun t => GoodTree in1 in2 t) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (in1_0 : Nat) (in2_0 : Nat) : OptionT Plausible.Gen BinaryTree :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              OptionTGen.thunkGen
                (fun _ =>
                  match DecOpt.decOpt (in1 = in1_0) initSize with
                  | Option.some Bool.true => pure BinaryTree.Leaf
                  | _ => OptionT.fail)),
            (1, OptionTGen.thunkGen (fun _ => OptionT.fail))]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              OptionTGen.thunkGen
                (fun _ =>
                  match DecOpt.decOpt (in1 = in1_0) initSize with
                  | Option.some Bool.true => pure BinaryTree.Leaf
                  | _ => OptionT.fail))]
    fun size => aux_arb size size in1 in2
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (t : BinaryTree) => GoodTree in1 in2 t)
