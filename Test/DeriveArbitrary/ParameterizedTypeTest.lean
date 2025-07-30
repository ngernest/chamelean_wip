import Plausible.Arbitrary
import Plausible.DeriveArbitrary
import Plausible.Attr

open Plausible

/-- A dummy `inductive` type isomorphic to the polymorphic `List` type,
    used as an example of a parameterized inductive type -/
inductive MyList (α : Type) where
  | MyNil : MyList α
  | MyCons : α → MyList α → MyList α

-- set_option trace.Elab.Deriving.hashable true in
-- deriving instance Hashable for MyList


set_option trace.plausible.deriving.arbitrary true in
/--
trace: [plausible.deriving.arbitrary] ⏎
    [mutual
       def arbitraryMyList✝ {α✝} [Plausible.ArbitraryFueled✝ α✝] : Nat → Plausible.Gen (@MyList✝ α✝) :=
         let rec aux_arb (fuel : Nat) : Plausible.Gen (@MyList✝ α✝) :=
           match fuel with
           | Nat.zero => Plausible.Gen.oneOfWithDefault (pure MyList.MyNil) [(pure MyList.MyNil)]
           | fuel' + 1 =>
             Plausible.Gen.frequency (pure MyList.MyNil)
               [(1, (pure MyList.MyNil)),
                 (fuel' + 1,
                   (do
                     let a_0✝ ← Plausible.Arbitrary.arbitrary
                     let a_0✝¹ ← aux_arb fuel'
                     return MyList.MyCons a_0✝ a_0✝¹))]
         fun fuel => aux_arb fuel
     end,
     instance {α✝} [Plausible.ArbitraryFueled✝ α✝] : Plausible.ArbitraryFueled✝ (@MyList✝ α✝) :=
       ⟨arbitraryMyList✝⟩]
-/
#guard_msgs in
deriving instance Arbitrary for MyList
