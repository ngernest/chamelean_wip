
import Plausible.Gen
import Plausible.New.OptionTGen
import Plausible.New.DecOpt
import Plausible.New.ArbitrarySizedSuchThat
import Plausible.GeneratingGoodGenerators.DeriveSubGenerator
import Test.CommonDefinitions.BinaryTree

open ArbitrarySizedSuchThat OptionTGen

set_option guard_msgs.diff true

-- `balancedTree n t` describes whether the tree `t` of height `n` is *balancedTree*, i.e. every path through the tree has length either `n` or `n-1`. -/
inductive balancedTree : Nat → BinaryTree → Prop where
  | B0 : balancedTree .zero BinaryTree.Leaf
  | B1 : balancedTree (.succ .zero) BinaryTree.Leaf
  | BS : ∀ n x l r,
    balancedTree n l → balancedTree n r →
    balancedTree (.succ n) (BinaryTree.Node x l r)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat BinaryTree (fun t_1 => balancedTree n_1 t_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (n_1 : Nat) : OptionT Plausible.Gen BinaryTree :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              match n_1 with
              | Nat.zero => return BinaryTree.Leaf
              | _ => OptionT.fail),
            (1,
              match n_1 with
              | Nat.succ (Nat.zero) => return BinaryTree.Leaf
              | _ => OptionT.fail)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              match n_1 with
              | Nat.zero => return BinaryTree.Leaf
              | _ => OptionT.fail),
            (1,
              match n_1 with
              | Nat.succ (Nat.zero) => return BinaryTree.Leaf
              | _ => OptionT.fail),
            (Nat.succ size',
              match n_1 with
              | Nat.succ n => do
                let l ← aux_arb initSize size' n;
                do
                  let r ← aux_arb initSize size' n;
                  do
                    let x ← Arbitrary.arbitrary;
                    return BinaryTree.Node x l r
              | _ => OptionT.fail)]
    fun size => aux_arb size size n_1
-/
#guard_msgs(info, drop warning) in
#derive_scheduled_generator (fun (t : BinaryTree) => balancedTree n t)
