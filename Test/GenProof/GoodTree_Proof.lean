import Plausible.IR.Examples
import Plausible.New.GenProofTactics
import Plausible.New.OptionTGenTheorems
open Plausible
open OptionTGen

inductive GoodTree : Nat → Nat → Tree → Prop where
  | GoodLeaf : ∀ n, GoodTree n n .Leaf


def genGoodTree (in1_0 : Nat) (in2_0 : Nat) : Nat → OptionT Plausible.Gen Tree :=
  let rec aux_arb (initSize : Nat) (size : Nat) (in1_0 : Nat) (in2_0 : Nat) : OptionT Plausible.Gen Tree :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              OptionTGen.thunkGen
                (fun _ =>
                  match DecOpt.decOpt (in2_0 = in1_0) initSize with
                  | Option.some Bool.true => pure Tree.Leaf
                  | _ => OptionT.fail)),
            (1, OptionTGen.thunkGen (fun _ => OptionT.fail))]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              OptionTGen.thunkGen
                (fun _ =>
                  match DecOpt.decOpt (in2_0  = in1_0) initSize with
                  | Option.some Bool.true => pure Tree.Leaf
                  | _ => OptionT.fail))]
  fun size => aux_arb size size in1_0 in2_0


theorem genGoodTree_correct: OptionTGenEnsure (GoodTree in1 in2) (genGoodTree in1 in2 size) := by
  gen_proof
