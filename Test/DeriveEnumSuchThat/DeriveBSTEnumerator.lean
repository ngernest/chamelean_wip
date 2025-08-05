import Plausible.New.DecOpt
import Plausible.New.Enumerators
import Plausible.New.DeriveEnumSuchThat
import Plausible.New.EnumeratorCombinators
import Test.DeriveArbitrarySuchThat.DeriveBSTGenerator

set_option guard_msgs.diff true

/--
info: Try this enumerator: instance : EnumSizedSuchThat Nat (fun x => Between lo x hi) where
  enumSizedST :=
    let rec aux_enum (initSize : Nat) (size : Nat) (lo_1 : Nat) (hi_1 : Nat) : OptionT Enumerator Nat :=
      match size with
      | Nat.zero =>
        EnumeratorCombinators.enumerate
          [match hi_1 with
            | Nat.succ (Nat.succ m) => pure (Nat.succ lo_1)
            | _ => OptionT.fail,
            OptionT.fail]
      | Nat.succ size' =>
        EnumeratorCombinators.enumerate
          [match hi_1 with
            | Nat.succ (Nat.succ m) => pure (Nat.succ lo_1)
            | _ => OptionT.fail,
            match hi_1 with
            | Nat.succ o => do
              let m ← aux_enum initSize size' lo_1 o
              return Nat.succ m
            | _ => OptionT.fail]
    fun size => aux_enum size size lo hi
-/
#guard_msgs(info, drop warning) in
#derive_enumerator (fun (x : Nat) => Between lo x hi)

/--
info: Try this enumerator: instance : EnumSizedSuchThat BinaryTree (fun t => BST lo hi t) where
  enumSizedST :=
    let rec aux_enum (initSize : Nat) (size : Nat) (lo_1 : Nat) (hi_1 : Nat) : OptionT Enumerator BinaryTree :=
      match size with
      | Nat.zero => EnumeratorCombinators.enumerate [pure BinaryTree.Leaf, OptionT.fail]
      | Nat.succ size' =>
        EnumeratorCombinators.enumerate
          [pure BinaryTree.Leaf, do
            let x ← EnumSuchThat.enumST (fun x => Between lo_1 x hi_1)
            let l ← aux_enum initSize size' lo_1 x
            let r ← aux_enum initSize size' x hi_1
            return BinaryTree.Node x l r]
    fun size => aux_enum size size lo hi
-/
#guard_msgs(info, drop warning) in
#derive_enumerator (fun (t : BinaryTree) => BST lo hi t)
