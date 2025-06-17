# Plausible
A property testing framework for Lean 4 that integrates into the tactic framework.

## New Metaprogramming Code
See the [`New`](./Plausible/New/) subdirectory for code that uses Lean's metaprogramming facilities (`TSyntax`) 
to automatically derive generators/checkers for inductive relations, à la [Paraskevopoulou et al. 2022](https://lemonidas.github.io/pdf/ComputingCorrectly.pdf).

Repo overview:
- [`Examples.lean`](./Plausible/IR/Examples.lean): Some example inductive relations (BSTs, balanced trees, STLC)
- [`OptionTGen.lean`](./Plausible/New/OptionTGen.lean): Generator combinators that work over the `OptionT Gen` monad transformer (representing generators that may fail) + example generators for BSTs/balanced trees 
- [`DecOpt.lean`](./Plausible/New/DecOpt.lean): The `DecOpt` typeclass for partially decidable propositions, adapted from QuickChick
- [`GenSuchThat.lean`](./Plausible/New/GenSuchThat.lean): The `GenSuchThat` & `GenSizedSuchThat` typeclasses for constrained generators (generators of values satisfying a proposition), adapted from QuickChick
- [`GeneratorCombinators.lean`](./Plausible/New/GeneratorCombinators.lean): Extra combinators for Plausible generators (e.g. analogs of the `sized` and `frequency` combinators from Haskell QuickCheck)
- [`STLC.lean`](./Plausible/New/STLC.lean): Example checkers & generators for well-typed STLC terms
- [`DeriveGenerator.lean`](./Plausible/New/DeriveGenerator.lean): Metaprogramming infrastructure for automatically deriving Plausible generators
- [`SubGenerators.lean`](./Plausible/New/SubGenerators.lean): Handles constraints when deriving sub-generators
- [`TSyntaxCombinators.lean`](./Plausible/New/TSyntaxCombinators.lean): Combinators over `TSyntax` for creating monadic `do`-blocks & other Lean expressions via metaprogramming
- [`DeriveChecker.lean`](./Plausible/New/DeriveChecker.lean): Metaprogramming infrastructure for automatically deriving checkers
- [`Idents.lean`](./Plausible/New/Idents.lean): Utilities for dealing with identifiers / producing fresh names 
- [`Tests.lean`](./Plausible/New/Tests.lean): Example usage on how to use the new `#deriving` commands for deriving generators

## Usage
If you are using built in types Plausible is usually able to handle them already:
```lean
import Plausible

example (xs ys : Array Nat) : xs.size = ys.size → xs = ys := by
  /--
  ===================
  Found a counter-example!
  xs := #[0]
  ys := #[1]
  guard: 1 = 1
  issue: #[0] = #[1] does not hold
  (0 shrinks)
  -------------------
  -/
  plausible

#eval Plausible.Testable.check <| ∀ (xs ys : Array Nat), xs.size = ys.size → xs = ys
```

If you are defining your own type it needs instances of `Repr`, `Plausible.Shrinkable` and
`Plausible.SampleableExt`:
```lean
import Plausible

open Plausible

structure MyType where
  x : Nat
  y : Nat
  h : x ≤ y
  deriving Repr

instance : Shrinkable MyType where
  shrink := fun ⟨x, y, _⟩ =>
    let proxy := Shrinkable.shrink (x, y - x)
    proxy.map (fun (fst, snd) => ⟨fst, fst + snd, by omega⟩)

instance : SampleableExt MyType :=
  SampleableExt.mkSelfContained do
    let x ← SampleableExt.interpSample Nat
    let xyDiff ← SampleableExt.interpSample Nat
    return ⟨x, x + xyDiff, by omega⟩

-- No counter example found
#eval Testable.check <| ∀ a b : MyType, a.y ≤ b.x → a.x ≤ b.y
```
For more documentation refer to the module docs.
