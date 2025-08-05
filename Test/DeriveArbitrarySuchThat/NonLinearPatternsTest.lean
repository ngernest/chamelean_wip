
import Plausible.Gen
import Plausible.New.OptionTGen
import Plausible.New.DecOpt
import Plausible.New.ArbitrarySizedSuchThat
import Plausible.GeneratingGoodGenerators.DeriveSubGenerator
import Test.CommonDefinitions.BinaryTree


open ArbitrarySizedSuchThat OptionTGen

set_option guard_msgs.diff true

-- Example taken from "Generating Good Generators for Inductive Relations", section 3
inductive GoodTree : Nat → Nat → BinaryTree → Prop where
  | GoodLeaf : ∀ n, GoodTree n n .Leaf

/--
info: Try this generator: instance : ArbitrarySizedSuchThat BinaryTree (fun t_1 => GoodTree in1_1 in2_1 t_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (in1_1 : Nat) (in2_1 : Nat) : OptionT Plausible.Gen BinaryTree :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              match DecOpt.decOpt (BEq.beq in1_1 in2_1) initSize with
              | Option.some Bool.true => return BinaryTree.Leaf
              | _ => OptionT.fail)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              match DecOpt.decOpt (BEq.beq in1_1 in2_1) initSize with
              | Option.some Bool.true => return BinaryTree.Leaf
              | _ => OptionT.fail),
            ]
    fun size => aux_arb size size in1_1 in2_1
-/
#guard_msgs(info, drop warning) in
#derive_scheduled_generator (fun (t : BinaryTree) => GoodTree in1 in2 t)
