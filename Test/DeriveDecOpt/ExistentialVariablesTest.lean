
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

/--
info: Try this checker: instance : DecOpt (NatChain a b) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (a_0 : Nat) (b_0 : Nat) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            EnumeratorCombinators.enumerating Enum.enum
              (fun x =>
                EnumeratorCombinators.enumerating Enum.enum
                  (fun y =>
                    DecOpt.andOptList
                      [DecOpt.decOpt (@LT.lt Nat instLTNat a x) initSize,
                        DecOpt.decOpt (@LT.lt Nat instLTNat x y) initSize,
                        DecOpt.decOpt (@LT.lt Nat instLTNat y b) initSize])
                  initSize)
              initSize]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            EnumeratorCombinators.enumerating Enum.enum
              (fun x =>
                EnumeratorCombinators.enumerating Enum.enum
                  (fun y =>
                    DecOpt.andOptList
                      [DecOpt.decOpt (@LT.lt Nat instLTNat a x) initSize,
                        DecOpt.decOpt (@LT.lt Nat instLTNat x y) initSize,
                        DecOpt.decOpt (@LT.lt Nat instLTNat y b) initSize])
                  initSize)
              initSize]
    fun size => aux_dec size size a b
-/
#guard_msgs(info, drop warning) in
#derive_checker (NatChain a b)
