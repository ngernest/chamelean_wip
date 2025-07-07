
import Plausible.New.OptionTGen
import Plausible.New.DecOpt
import Plausible.New.Enumerators
import Plausible.New.DeriveEnumSuchThat
import Plausible.New.EnumeratorCombinators
import Test.DeriveArbitrarySuchThat.DeriveBalancedTreeGenerator

set_option guard_msgs.diff true

/--
info: Try this generator: instance : EnumSizedSuchThat BinaryTree (fun t => balancedTree n t) where
  enumSizedST :=
    let rec aux_enum (initSize : Nat) (size : Nat) (n_0 : Nat) : OptionT Enumerator BinaryTree :=
      match size with
      | Nat.zero =>
        EnumeratorCombinators.enumerate
          [match n_0 with
            | 0 => pure BinaryTree.Leaf
            | _ => OptionT.fail,
            match n_0 with
            | 1 => pure BinaryTree.Leaf
            | _ => OptionT.fail,
            OptionT.fail]
      | Nat.succ size' =>
        EnumeratorCombinators.enumerate
          [match n_0 with
            | 0 => pure BinaryTree.Leaf
            | _ => OptionT.fail,
            match n_0 with
            | 1 => pure BinaryTree.Leaf
            | _ => OptionT.fail,
            match n_0 with
            | Nat.succ n => do
              let l ← aux_enum initSize size' n
              let r ← aux_enum initSize size' n
              let x ← Enum.enum
              return BinaryTree.Node x l r
            | _ => OptionT.fail]
    fun size => aux_enum size size n
-/
#guard_msgs(info, drop warning) in
#derive_enumerator (fun (t : BinaryTree) => balancedTree n t)
