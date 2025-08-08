
import Plausible.Gen
import Plausible.Chamelean.OptionTGen
import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.ArbitrarySizedSuchThat
import Plausible.Chamelean.DeriveConstrainedProducer
import Test.CommonDefinitions.BinaryTree

open ArbitrarySizedSuchThat OptionTGen

set_option guard_msgs.diff true

/-- `Between lo x hi` means `lo < x < hi` -/
inductive Between : Nat -> Nat -> Nat -> Prop where
| BetweenN : ∀ n m, n <= m -> Between n (.succ n) (.succ (.succ m))
| BetweenS : ∀ n m o,
  Between n m o -> Between n (.succ m) (.succ o)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat Nat (fun x_1 => Between lo_1 x_1 hi_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (lo_1 : Nat) (hi_1 : Nat) : OptionT Plausible.Gen Nat :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              match hi_1 with
              | Nat.succ (Nat.succ m) =>
                match DecOpt.decOpt (LE.le lo_1 m) initSize with
                | Option.some Bool.true => return Nat.succ lo_1
                | _ => OptionT.fail
              | _ => OptionT.fail)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              match hi_1 with
              | Nat.succ (Nat.succ m) =>
                match DecOpt.decOpt (LE.le lo_1 m) initSize with
                | Option.some Bool.true => return Nat.succ lo_1
                | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match hi_1 with
              | Nat.succ o => do
                let m ← aux_arb initSize size' lo_1 o;
                return Nat.succ m
              | _ => OptionT.fail)]
    fun size => aux_arb size size lo_1 hi_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (x : Nat) => Between lo x hi)

/-- `BST lo hi t` describes whether a tree `t` is a BST that contains values strictly within `lo` and `hi` -/
inductive BST : Nat → Nat → BinaryTree → Prop where
  | BstLeaf: BST lo hi .Leaf
  | BstNode: ∀ lo hi x l r,
    Between lo x hi →
    BST lo x l →
    BST x hi r →
    BST lo hi (.Node x l r)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat BinaryTree (fun t_1 => BST lo_1 hi_1 t_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (lo_1 : Nat) (hi_1 : Nat) : OptionT Plausible.Gen BinaryTree :=
      match size with
      | Nat.zero => OptionTGen.backtrack [(1, return BinaryTree.Leaf)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1, return BinaryTree.Leaf),
            (Nat.succ size', do
              let x ← ArbitrarySizedSuchThat.arbitrarySizedST (fun x => Between lo_1 x hi_1) initSize;
              do
                let l ← aux_arb initSize size' lo_1 x;
                do
                  let r ← aux_arb initSize size' x hi_1;
                  return BinaryTree.Node x l r)]
    fun size => aux_arb size size lo_1 hi_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (t : BinaryTree) => BST lo hi t)
