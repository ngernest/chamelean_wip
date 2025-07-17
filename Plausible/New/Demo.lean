import Plausible.New.DeriveArbitrarySuchThat
import Plausible.New.Arbitrary
import Plausible.New.Enum
import Plausible.New.DeriveArbitrary
import Plausible.New.DeriveEnum
import Plausible.New.ArbitrarySizedSuchThat

-- Binary trees
inductive Tree
  | Leaf : Tree
  | Node : Nat → Tree → Tree → Tree
  deriving Arbitrary, Enum

inductive Permutation : List Nat → List Nat → Prop where
  | Trans : forall l1 l2 l3,
    Permutation l1 l2 ->
    Permutation l2 l3 ->
    Permutation l1 l3
