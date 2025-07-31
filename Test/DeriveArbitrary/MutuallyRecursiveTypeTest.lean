import Plausible.Arbitrary
import Plausible.DeriveArbitrary
import Plausible.Attr
import Plausible.Testable

open Plausible

/-
# Testing the deriving `Arbitrary` handler on mutually recursive inductive types

To test that our derived generators can handle mutually recursive types,
we define two mutually recursive types (one `inductive` and one `structure`)
to represent a binary tree.

(Example adapted from Cornell CS 3110 lecture notes
https://www.cs.cornell.edu/courses/cs3110/2008fa/lectures/lec04.html)

```lean
mutual
  inductive NatTree
    | Empty : NatTree
    | Node : Node → NatTree
    deriving Nonempty

  structure Node where
    value : Nat
    left : NatTree
    right : NatTree
    deriving Nonempty
end
```

Note that the user needs to add the `deriving Nonempty` annotation
to each type in the mutually recursive definition -- this is needed
in order to convince Lean that the type `Nat → Plausible.Gen NatTree`
is empty during the derivation process.

-/

mutual
  /-- A (possibly empty) binary tree -/
  inductive NatTree
    | Empty : NatTree
    | Node : Node → NatTree
    deriving Nonempty, Repr

  /-- A child node in a tree, containing a value and two subtrees -/
  structure Node where
    value : Nat
    left : NatTree
    right : NatTree
    deriving Nonempty
end


set_option trace.plausible.deriving.arbitrary true in
/--
trace: [plausible.deriving.arbitrary] ⏎
    [mutual
       partial def arbitraryNatTree✝ : Nat → Plausible.Gen (@NatTree✝) :=
         let localinst✝ : Plausible.ArbitraryFueled✝ (@NatTree✝) := ⟨arbitraryNatTree✝⟩;
         let localinst✝¹ : Plausible.ArbitraryFueled✝ (@Node✝) := ⟨arbitraryNode✝⟩;
         let rec aux_arb (fuel : Nat) : Plausible.Gen (@NatTree✝) :=
           match fuel with
           | Nat.zero =>
             Plausible.Gen.oneOfWithDefault (pure NatTree.Empty)
               [(pure NatTree.Empty),
                 (do
                   let a_0✝ ← Plausible.Arbitrary.arbitrary
                   return NatTree.Node a_0✝)]
           | fuel' + 1 =>
             Plausible.Gen.frequency (pure NatTree.Empty)
               [(1, (pure NatTree.Empty)),
                 (1,
                   (do
                     let a_0✝ ← Plausible.Arbitrary.arbitrary
                     return NatTree.Node a_0✝)),
                 ]
         fun fuel => aux_arb fuel
       partial def arbitraryNode✝ : Nat → Plausible.Gen (@Node✝) :=
         let localinst✝² : Plausible.ArbitraryFueled✝ (@NatTree✝) := ⟨arbitraryNatTree✝⟩;
         let localinst✝³ : Plausible.ArbitraryFueled✝ (@Node✝) := ⟨arbitraryNode✝⟩;
         let rec aux_arb (fuel : Nat) : Plausible.Gen (@Node✝) :=
           match fuel with
           | Nat.zero =>
             Plausible.Gen.oneOfWithDefault
               (do
                 let a_0✝¹ ← Plausible.Arbitrary.arbitrary
                 let a_0✝² ← Plausible.Arbitrary.arbitrary
                 let a_0✝³ ← Plausible.Arbitrary.arbitrary
                 return Node.mk a_0✝¹ a_0✝² a_0✝³)
               [(do
                   let a_0✝¹ ← Plausible.Arbitrary.arbitrary
                   let a_0✝² ← Plausible.Arbitrary.arbitrary
                   let a_0✝³ ← Plausible.Arbitrary.arbitrary
                   return Node.mk a_0✝¹ a_0✝² a_0✝³)]
           | fuel' + 1 =>
             Plausible.Gen.frequency
               (do
                 let a_0✝¹ ← Plausible.Arbitrary.arbitrary
                 let a_0✝² ← Plausible.Arbitrary.arbitrary
                 let a_0✝³ ← Plausible.Arbitrary.arbitrary
                 return Node.mk a_0✝¹ a_0✝² a_0✝³)
               [(1,
                   (do
                     let a_0✝¹ ← Plausible.Arbitrary.arbitrary
                     let a_0✝² ← Plausible.Arbitrary.arbitrary
                     let a_0✝³ ← Plausible.Arbitrary.arbitrary
                     return Node.mk a_0✝¹ a_0✝² a_0✝³)),
                 ]
         fun fuel => aux_arb fuel
     end,
     instance : Plausible.ArbitraryFueled✝ (@NatTree✝) :=
       ⟨arbitraryNatTree✝⟩]
-/
#guard_msgs in
deriving instance Arbitrary for NatTree

-- Test that we can successfully synthesize instances of `Arbitrary` & `ArbitraryFueled`

/-- info: instArbitraryFueledNatTree -/
#guard_msgs in
#synth ArbitraryFueled NatTree

/-- info: instArbitraryOfArbitraryFueled -/
#guard_msgs in
#synth Arbitrary NatTree

/-- `search tree x` recursively searches for a value `x` in `tree`,
    returning a `Bool` indicating `x`'s membership in `tree`

    (Note that `tree` may not obey the binary search tree
    invariant, so this algorithm is not the most efficient.) -/
def search (tree : NatTree) (x : Nat) : Bool :=
  match tree with
  | .Empty => false
  | .Node { value, left, right } =>
    value == x || search left x || search right x

/-- `Shrinkable` instance for `NatTree` -/
instance : Shrinkable NatTree where
  shrink (tree : NatTree) :=
    match tree with
    | .Empty => []
    | .Node _ => [.Empty]

/-- `SampleableExt` instance for `NatTree` -/
instance : SampleableExt NatTree :=
  SampleableExt.mkSelfContained Arbitrary.arbitrary


/-!
To test whether the derived generator can generate counterexamples,
we create an erroneous property `∀ tree : NatTree, search tree 5`,
and ask Plausible to falsify it.

(This property is false, since there exist trees which don't contain the value 5,
e.g. the `Empty` tree.)

-/

/-- error: Found a counter-example! -/
#guard_msgs in
#eval Testable.check (∀ tree : NatTree, search tree 5)
  (cfg := {numInst := 10, maxSize := 2, quiet := true})
