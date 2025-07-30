import Plausible

open Plausible Gen

set_option guard_msgs.diff true

/-- A binary tree is either a single `Leaf`,
    or a `Node` containing a `Nat` with left & right sub-trees -/
inductive Tree where
| Leaf : Tree
| Node : Nat → Tree → Tree → Tree
deriving BEq, Repr

-- Invoke deriving instance handler for the `Arbitrary` typeclass on `type` and `term`
set_option trace.plausible.deriving.arbitrary true in
/--
trace: [plausible.deriving.arbitrary] Derived generator: instance : Plausible.ArbitraryFueled Tree where
      arbitraryFueled :=
        let rec aux_arb (fuel : Nat) : Plausible.Gen Tree :=
          match fuel with
          | Nat.zero => Plausible.Gen.oneOfWithDefault (pure Tree.Leaf) [(pure Tree.Leaf)]
          | fuel' + 1 =>
            Plausible.Gen.frequency (pure Tree.Leaf)
              [(1, (pure Tree.Leaf)),
                (fuel' + 1,
                  (do
                    let a_0 ← Plausible.Arbitrary.arbitrary
                    let a_1 ← aux_arb fuel'
                    let a_2 ← aux_arb fuel'
                    return Tree.Node a_0 a_1 a_2))]
        fun fuel => aux_arb fuel
-/
#guard_msgs in
deriving instance Arbitrary for Tree

-- Test that we can successfully synthefuel instances of `Arbitrary` & `ArbitraryFueled`

/-- info: instArbitraryFueledTree -/
#guard_msgs in
#synth ArbitraryFueled Tree

/-- info: instArbitraryOfArbitraryFueled -/
#guard_msgs in
#synth Arbitrary Tree

-- Test that we can use the derived generator

/-- Mirrors a tree, i.e. interchanges the left & right children of all `Node`s -/
def mirror (t : Tree) : Tree :=
  match t with
  | .Leaf => .Leaf
  | .Node x l r => .Node x r l

/-- `Shrinkable` instance for `Tree` -/
instance shrinkTree : Shrinkable Tree where
  shrink (t : Tree) :=
    match t with
    | .Leaf => []
    | .Node _ _ _ => [.Leaf]

/-- `SampleableExt` instance for `Tree` -/
instance : SampleableExt Tree where
  proxy := Tree
  proxyRepr := inferInstance
  shrink := shrinkTree
  sample := Arbitrary.arbitrary
  interp := id

-- Mirroring a tree twice should yield the original tree
--  Test that we can succesfully generate a counterexample to the following (erroneous) property

/-- error: Found a counter-example! -/
#guard_msgs in
#eval Testable.check (∀ t : Tree, mirror (mirror t) != t)
  (cfg := {numInst := 10, maxSize := 5, quiet := true})
