
import Plausible.New.OptionTGen
import Plausible.New.DecOpt
import Plausible.New.Enumerators
import Plausible.New.DeriveScheduledGenerator
import Plausible.New.EnumeratorCombinators
import Test.DeriveArbitrarySuchThat.DeriveBalancedTreeGenerator

set_option guard_msgs.diff true

/--
info: Try this enumerator: instance : EnumSizedSuchThat BinaryTree (fun t_1 => balancedTree n_1 t_1) where
  enumSizedST :=
    let rec aux_enum (initSize : Nat) (size : Nat) (n_1 : Nat) : OptionT Enumerator BinaryTree :=
      match size with
      | Nat.zero =>
        EnumeratorCombinators.enumerate
          [match n_1 with
            | Nat.zero => return BinaryTree.Leaf
            | _ => OptionT.fail,
            match n_1 with
            | Nat.succ (Nat.zero) => return BinaryTree.Leaf
            | _ => OptionT.fail]
      | Nat.succ size' =>
        EnumeratorCombinators.enumerate
          [match n_1 with
            | Nat.zero => return BinaryTree.Leaf
            | _ => OptionT.fail,
            match n_1 with
            | Nat.succ (Nat.zero) => return BinaryTree.Leaf
            | _ => OptionT.fail,
            match n_1 with
            | Nat.succ n => do
              let l ← aux_enum initSize size' n;
              do
                let r ← aux_enum initSize size' n;
                do
                  let x ← Enum.enum;
                  return BinaryTree.Node x l r
            | _ => OptionT.fail]
    fun size => aux_enum size size n_1
-/
#guard_msgs(info, drop warning) in
#derive_scheduled_enumerator (fun (t : BinaryTree) => balancedTree n t)
