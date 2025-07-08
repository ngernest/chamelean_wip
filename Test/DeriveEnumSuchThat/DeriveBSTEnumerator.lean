import Plausible.New.DecOpt
import Plausible.New.Enumerators
import Plausible.New.DeriveEnumSuchThat
import Plausible.New.EnumeratorCombinators
import Test.DeriveArbitrarySuchThat.DeriveBSTGenerator

set_option guard_msgs.diff true

/--
info: Try this enumerator: instance : EnumSizedSuchThat BinaryTree (fun t => BST lo hi t) where
  enumSizedST :=
    let rec aux_enum (initSize : Nat) (size : Nat) (lo_1 : Nat) (hi_1 : Nat) : OptionT Enumerator BinaryTree :=
      match size with
      | Nat.zero => EnumeratorCombinators.enumerate [pure BinaryTree.Leaf, OptionT.fail]
      | Nat.succ size' =>
        EnumeratorCombinators.enumerate
          [pure BinaryTree.Leaf, do
            let x ← Enum.enum
            let l ← aux_enum initSize size' lo_1 x
            let r ← aux_enum initSize size' x hi_1
            if lo_1 < x && x < hi_1 then ⏎
              return BinaryTree.Node x l r
            else
              OptionT.fail]
    fun size => aux_enum size size lo hi
-/
#guard_msgs(info, drop warning) in
#derive_enumerator (fun (t : BinaryTree) => BST lo hi t)
