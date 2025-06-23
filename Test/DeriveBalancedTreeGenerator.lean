
import Plausible.Gen
import Plausible.New.OptionTGen
import Plausible.New.DecOpt
import Plausible.New.ArbitrarySizedSuchThat
import Plausible.New.DeriveGenerator
import Test.DeriveBSTGenerator

open ArbitrarySizedSuchThat OptionTGen

set_option guard_msgs.diff true

-- `balancedTree n t` describes whether the tree `t` of height `n` is *balancedTree*, i.e. every path through the tree has length either `n` or `n-1`. -/
inductive balancedTree : Nat → BinaryTree → Prop where
  | B0 : balancedTree 0 BinaryTree.Leaf
  | B1 : balancedTree 1 BinaryTree.Leaf
  | BS : ∀ n x l r,
    balancedTree n l → balancedTree n r →
    balancedTree (.succ n) (BinaryTree.Node x l r)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat BinaryTree (fun t => balancedTree n t) where
  genSizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (n_0 : Nat) : OptionT Plausible.Gen BinaryTree :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              OptionTGen.thunkGen
                (fun _ =>
                  match n_0 with
                  | 0 => pure BinaryTree.Leaf
                  | _ => OptionT.fail)),
            (1,
              OptionTGen.thunkGen
                (fun _ =>
                  match n_0 with
                  | 1 => pure BinaryTree.Leaf
                  | _ => OptionT.fail)),
            (1, OptionTGen.thunkGen (fun _ => OptionT.fail))]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              OptionTGen.thunkGen
                (fun _ =>
                  match n_0 with
                  | 0 => pure BinaryTree.Leaf
                  | _ => OptionT.fail)),
            (1,
              OptionTGen.thunkGen
                (fun _ =>
                  match n_0 with
                  | 1 => pure BinaryTree.Leaf
                  | _ => OptionT.fail)),
            (Nat.succ size',
              OptionTGen.thunkGen
                (fun _ =>
                  match n_0 with
                  | Nat.succ n => do
                    let l ← aux_arb initSize size' n
                    let r ← aux_arb initSize size' n
                    let x ← Plausible.SampleableExt.interpSample Nat
                    return BinaryTree.Node x l r
                  | _ => OptionT.fail))]
    fun size => aux_arb size size n
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (t : BinaryTree) => balancedTree n t)
