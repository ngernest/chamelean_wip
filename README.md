# Chamelean 
An extension of Lean's Plausible property-based testing library which automatically derives
checkers / enumerators / generators for inductive relations.

(See the [`New`](./Plausible/New/) subdirectory for code that uses Lean's metaprogramming facilities (`TSyntax`) 
to perform this procedure.)

Our design is heavily inspired by [Coq/Rocq's QuickChick](https://github.com/QuickChick/QuickChick) library and the following papers:
- [Computing Correctly with Inductive Relations (PLDI 2022)](https://lemonidas.github.io/pdf/ComputingCorrectly.pdf)
- [Generating Good Generators for Inductive Relations (POPL 2018)](https://lemonidas.github.io/pdf/GeneratingGoodGenerators.pdf)


## Overview
Like QuickChick & [Haskell QuickChick](https://hackage.haskell.org/package/QuickCheck), we provide the following typeclasses for random generation:
- `Arbitrary`: random generators for inhabitants of algebraic data types
- `ArbitrarySuchThat`: generators which only produce random values that satisfy a user-supplied inductive relation
- `ArbitrarySized`, `ArbitrarySizedSuchThat`: versions of the two typeclasses above where the generator's size parameter is made explicit 

We provide two top-level commands which automatically derive generators for Lean `inductive`s:

**1. Deriving unconstrained generators**              
An *unconstrained* generator produces random inhabitants of an algebraic data type. 
We provide two frontends which derive instances of `Arbitrary` & `ArbitrarySuchThat` respectively: 

**1a. Deriving Instance** (for algebraic data types)              
Users can write `deriving Arbitrary` after an inductive type definition:

```lean 
inductive Tree where
  ...
  deriving Arbitrary 
```

Alternatively, users can also write `deriving instance Arbitrary for T1, ..., Tn` as a top-level command 
to derive `Arbitrary` instances for types `T1, ..., Tn` simultaneously.

**1b. Command Elaborator**            
We provide a command elaborator which elaborates the `#derive_arbitrary` command: 

```lean
-- `#derive_arbitrary` derives an instance of `Arbitrary` for the `Tree` datatype
#derive_arbitrary Tree  
```

Regardless of which frontend is used, to sample from the derived generator, users can simply call `runArbitrary` and specify some 
`Nat` to act as the generator's size parameter (`10` in the example below):

```lean
#eval runArbitrary (α := Tree) 10
```

**2. Deriving constrained generators** (for inductive relations)                
A *constrained* generator only produces random values that satisfy a user-specified inductive relation. 
We provide a command elaborator which elaborates the `#derive_generator` command:

```lean
-- `#derive_generator` derives a constrained generator for `Tree`s that are balanced at some height `n`,
-- where `balanced n t` is a user-defined inductive relation
#derive_generator (fun (t : Tree) => balanced n t) 
``

To sample from the derived generator, users invoke `runSizedGen` & specify the right 
instance of the `ArbitrarySizedSuchThat` typeclass (along with some `Nat` to act as the generator size):

```lean
#eval runSizedGen (ArbitrarySizedSuchThat.arbitrarySizedST (fun t => balanced 5 t)) 10
```

## Repo overview

**Typeclass definitions**:
- [`Arbitrary.lean`](./Plausible/New/Arbitrary.lean): The `Arbitrary` & `ArbitrarySized` typeclasses for unconstrained generators, adapted from QuickChick
- [`ArbitrarySizedSuchThat.lean`](./Plausible/New/ArbitrarySizedSuchThat.lean): The `ArbitrarySuchThat` & `ArbitrarySizedSuchThat` typeclasses for constrained generators, adapted from QuickChick
- [`DecOpt.lean`](./Plausible/New/DecOpt.lean): The `DecOpt` typeclass for partially decidable propositions, adapted from QuickChick
- [`Enumerators.lean`](./Plausible/New/Enumerators.lean): The `Enum, EnumSized, EnumSuchThat, EnumSizedSuchThat` typeclasses for constrained & unconstrained enumeration

**Combinators for generators & enumerators**:
- [`GeneratorCombinators.lean`](./Plausible/New/GeneratorCombinators.lean): Extra combinators for Plausible generators (e.g. analogs of the `sized` and `frequency` combinators from Haskell QuickCheck)
- [`OptionTGen.lean`](./Plausible/New/OptionTGen.lean): Generator combinators that work over the `OptionT Gen` monad transformer (representing generators that may fail)
- [`EnumeratorCombinators.lean`](./Plausible/New/EnumeratorCombinators.lean): Combinators over enumators 

**Metaprogramming infrastructure**:
- [`TSyntaxCombinators.lean`](./Plausible/New/TSyntaxCombinators.lean): Combinators over `TSyntax` for creating monadic `do`-blocks & other Lean expressions via metaprogramming
- [`DeriveArbitrary.lean`](./Plausible/New/DeriveArbitrary.lean): Metaprogramming infrastructure for deriving *unconstrained* generators (instances of the `ArbitrarySized` typeclass)
- [`DeriveGenerator.lean`](./Plausible/New/DeriveGenerator.lean): Metaprogramming infrastructure for deriving *constrained* generators (instances of the `ArbitrarySizedSuchThat` typeclass)
- [`SubGenerators.lean`](./Plausible/New/SubGenerators.lean): Handles constraints when deriving sub-generators
- [`DeriveChecker.lean`](./Plausible/New/DeriveChecker.lean): Metaprogramming infrastructure for automatically deriving checkers

**Miscellany**:
- [`LazyList.lean`](./Plausible/New/LazyList.lean): Implementation of lazy lists (used for enumerators)
- [`Idents.lean`](./Plausible/New/Idents.lean): Utilities for dealing with identifiers / producing fresh names 
- [`Utils.lean`](./Plausible/New/Utils.lean): Other miscellaneous utils

**Examples**:
- [`Examples.lean`](./Plausible/IR/Examples.lean): Some example inductive relations (BSTs, balanced trees, STLC)
- [`STLC.lean`](./Plausible/New/STLC.lean): Example checkers & generators for well-typed STLC terms
- [`Trees.lean`](./Plausible/New/Trees.lean): Example generators for balanced trees & BSTs
- [`DeriveRegExpGenerator.lean`](./Test/DeriveArbitrary/DeriveRegExpGenerator.lean): Example generators for regular expressions

**Tests**:      
- The [`Test`](./Test/) subdirectory contains [snapshot tests](https://www.cs.cornell.edu/~asampson/blog/turnt.html) (aka [expect tests](https://blog.janestreet.com/the-joy-of-expect-tests/)) for the `#derive_generator` & `#derive_arbitrary` command elaborators. 
- Run `lake test` to check that the derived generators in [`Test`](./Test/) typecheck, and that the code for the derived generators match the expected output.
- See [`DeriveBSTGenerator.lean`](./Test/DeriveArbitrarySuchThat/DeriveBSTGenerator.lean) & [`DeriveBalancedTreeGenerator.lean`](./Test/DeriveArbitrarySuchThat/DeriveBalancedTreeGenerator.lean) for examples of snapshot tests. Follow the template in these two files to add new snapshot test file, and remember to import the new test file in [`Test.lean`](./Test.lean) afterwards.



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
