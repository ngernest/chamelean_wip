
import Plausible.New.DecOpt
import Plausible.New.DeriveChecker
import Plausible.New.EnumeratorCombinators
import Test.DeriveArbitrarySuchThat.SimultaneousMatchingTests

open DecOpt

set_option guard_msgs.diff true

/-- `NatChain a b` means there is an ascending chain of `Nat`s under the usual `<` order,
    where `a` and `b` are the start and end of the chain respectively
    - This is a dummy inductive relation with multiple existentially quantified vairables
      (note how `x` and `y` don't appear in the conclusion of the `ChainExists` constructor) -/
inductive NatChain (a b : Nat) : Prop where
| ChainExists : ∀ (x y : Nat),
    (a < x) →
    (x < y) ->
    (y < b) →
    NatChain a b


-- Dummy `EnumSizedSuchThat` instances needed so that the derived checker below compiles
instance : EnumSizedSuchThat Nat (fun x => a < x) where
  enumSizedST := sorry

instance : EnumSizedSuchThat Nat (fun y => x < y) where
  enumSizedST := sorry

/--
info: Try this checker: instance : DecOpt (NatChain a_1 b_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (a_1 : Nat) (b_1 : Nat) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            EnumeratorCombinators.enumeratingOpt (EnumSizedSuchThat.enumSizedST (fun x => LT.lt a_1 x) initSize)
              (fun x =>
                EnumeratorCombinators.enumeratingOpt (EnumSizedSuchThat.enumSizedST (fun y => LT.lt x y) initSize)
                  (fun y => DecOpt.decOpt (LT.lt y b_1) initSize) initSize)
              initSize]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            EnumeratorCombinators.enumeratingOpt (EnumSizedSuchThat.enumSizedST (fun x => LT.lt a_1 x) initSize)
              (fun x =>
                EnumeratorCombinators.enumeratingOpt (EnumSizedSuchThat.enumSizedST (fun y => LT.lt x y) initSize)
                  (fun y => DecOpt.decOpt (LT.lt y b_1) initSize) initSize)
              initSize,
            ]
    fun size => aux_dec size size a_1 b_1
-/
#guard_msgs(info, drop warning) in
#derive_checker (NatChain a b)
