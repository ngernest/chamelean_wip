# Chamelean 
Chamelean is an extension of Lean's Plausible property-based testing library which automatically derives
generators, enumerators and checkers for inductive relations.

Our design is heavily inspired by [Coq/Rocq's QuickChick](https://github.com/QuickChick/QuickChick) library and the following papers:
- [*Computing Correctly with Inductive Relations* (PLDI 2022)](https://lemonidas.github.io/pdf/ComputingCorrectly.pdf)
- [*Generating Good Generators for Inductive Relations* (POPL 2018)](https://lemonidas.github.io/pdf/GeneratingGoodGenerators.pdf)
- *Testing Theorems, Fully Automatically* (under submission, 2025)

## Overview
Like QuickChick, we provide the following typeclasses:
- `Arbitrary`: unconstrained random generators for inhabitants of algebraic data types
- `ArbitrarySuchThat`: constrained generators which only produce random values that satisfy a user-supplied inductive relation
- `ArbitrarySized`, `ArbitrarySizedSuchThat`: versions of the two typeclasses above where the generator's size parameter is made explicit 
- `Enum, EnumSuchThat, EnumSized, EnumSizedSuchThat`: Like their `Arbitrary` counterparts but for deterministic enumerators instead
- `DecOpt`: Checkers (partial decision procedures that return `Option Bool`) for inductive propositions

We provide various top-level commands which automatically derive generators for Lean `inductive`s:

**1. Deriving unconstrained generators/enumerators**              
An *unconstrained* generator produces random inhabitants of an algebraic data type, while an unconstrained enumerator *enumerates* (deterministically) said inhabitants. 

We provide two frontends which derive instances of `Arbitrary` & `ArbitrarySuchThat` (resp. `Enum` & `EnumSuchThat`) respectively: 

**1a. Deriving Instances** (for algebraic data types)              
Users can write `deriving Arbitrary` and/or `deriving Enum` after an inductive type definition, i.e.
```lean 
inductive Foo where
  ...
  deriving Arbitrary
```
or 
```lean 
inductive Foo where 
  ...
  deriving Foo
```
Alternatively, users can also write `deriving instance Arbitrary for T1, ..., Tn` or `deriving instance Enum for T1, ...` as a top-level command to derive `Arbitrary` / `Enum` instances for types `T1, ..., Tn` simultaneously.

**1b. Command Elaborators**            
We provide command elaborators which elaborate the `#derive_arbitrary` & `#derive_enum` commands respectively: 

```lean
-- `#derive_arbitrary` derives an instance of `Arbitrary` for the `Tree` datatype
#derive_arbitrary Tree  

-- `#derive_enum` derives an instance of `Enum` for the `Tree` datatype
#derive_enum Tree
```

To sample from a derived generator, users can simply call `runArbitrary`, specify the type 
for the desired generated values and provide some `Nat` to act as the generator's size parameter (`10` in the example below):

```lean
#eval runArbitrary (α := Tree) 10
```

Similarly, to return the elements produced form a derived enumerator, users can call `runEnum` like so:
```lean
#eval runEnum (α := Tree) 10
```

**2. Deriving constrained generators** (for inductive relations)                
A *constrained* producer only produces values that satisfy a user-specified inductive relation. 
Constrained generators randomly sample values, while constrained enumerators enumerate them.

We provide two command elaborators for deriving constrained generators/enumerators:

```lean
-- `#derive_generator` & `#derive_enumerator` derive constrained generators/enumerators 
-- for `Tree`s that are balanced at some height `n`,
-- where `balanced n t` is a user-defined inductive relation
#derive_generator (fun (t : Tree) => balanced n t) 
#derive_enumerator (fun (t : Tree) => balanced n t)
```
To sample from the derived producer, users invoke `runSizedGen` / `runSizedEnum` & specify the right 
instance of the `ArbitrarySizedSuchThat` / `EnumSizedSuchThat` typeclass (along with some `Nat` to act as the generator size):

```lean
-- For generators:
#eval runSizedGen (ArbitrarySizedSuchThat.arbitrarySizedST (fun t => balanced 5 t)) 10

-- For enumerators:
-- (we recommend using a smaller `Nat` as the fuel for enumerators to avoid stack overflow)
#eval runSizedEnum (EnumSizedSuchThat.enumSizedST (fun t => balanced 5 t)) 3
```

**3. Deriving checkers (partial decision procedures)** (for inductively-defined propositions)                                 
A checker for an inductively-defined `Prop` is a `Nat -> Option Bool` function, which 
takes a `Nat` argument as fuel and returns `none` if it can't decide whether the `Prop` holds (e.g. it runs out of fuel),
and otherwise returns `some true/some false` depending on whether the `Prop` holds.

We provide a command elaborator which elaborates the `#derive_checker` command:

```lean
-- `#derive_checker` derives a checker which determines whether `Tree`s `t` satisfy the `balanced` inductive proposition mentioned above 
#derive_checker (balanced n t)
```

## Repo overview

**Building & compiling**:
- To compile, run `lake build` from the top-level repository.
- To run snapshot tests, run `lake test`.
- To run linter checks, run `lake lint`. 
  + This invokes the linter provided via the [Batteries](https://github.com/leanprover-community/batteries/tree/main) library.
  + Note that some linter warnings are suppressed in [`scripts/nolints.json`](./scripts/nolints.json).

**Typeclass definitions**:
- [`Arbitrary.lean`](./Plausible/Chamelean/Arbitrary.lean): The `Arbitrary` & `ArbitrarySized` typeclasses for unconstrained generators, adapted from QuickChick
- [`ArbitrarySizedSuchThat.lean`](./Plausible/Chamelean/ArbitrarySizedSuchThat.lean): The `ArbitrarySuchThat` & `ArbitrarySizedSuchThat` typeclasses for constrained generators, adapted from QuickChick
- [`DecOpt.lean`](./Plausible/Chamelean/DecOpt.lean): The `DecOpt` typeclass for partially decidable propositions, adapted from QuickChick
- [`Enumerators.lean`](./Plausible/Chamelean/Enumerators.lean): The `Enum, EnumSized, EnumSuchThat, EnumSizedSuchThat` typeclasses for constrained & unconstrained enumeration

**Combinators for generators & enumerators**:
- [`GeneratorCombinators.lean`](./Plausible/Chamelean/GeneratorCombinators.lean): Extra combinators for Plausible generators (e.g. analogs of the `sized` and `frequency` combinators from Haskell QuickCheck)
- [`OptionTGen.lean`](./Plausible/Chamelean/OptionTGen.lean): Generator combinators that work over the `OptionT Gen` monad transformer (representing generators that may fail)
- [`EnumeratorCombinators.lean`](./Plausible/Chamelean/EnumeratorCombinators.lean): Combinators over enumerators 

**Algorithm for deriving constrained producers & checkers** (adapted from the QuickChick papers):
- [`UnificationMonad.lean`](./Plausible/Chamelean/UnificationMonad.lean): The unification monad described in [*Generating Good Generators*](https://lemonidas.github.io/pdf/GeneratingGoodGenerators.pdf)
- [`Schedules.lean`](./Plausible/Chamelean/Schedules.lean): Type definitions for generator schedules, as described in *Testing Theorems*
- [`DeriveSchedules.lean`](./Plausible/Chamelean/DeriveSchedules.lean): Algorithm for deriving generator schedules, as described in *Testing Theorems* 
- [`DeriveConstrainedProducer.lean`](./Plausible/Chamelean/DeriveConstrainedProducer.lean): Algorithm for deriving constrained generators using the aforementioned unification algorithm & generator schedules
- [`MExp.lean`](./Plausible/Chamelean/MExp.lean): An intermediate representation for monadic expressions (`MExp`), used when compiling schedules to Lean code
- [`MakeConstrainedProducerInstance.lean`](./Plausible/Chamelean/MakeConstrainedProducerInstance.lean): Auxiliary functions for creating instances of typeclasses for constrained producers (`ArbitrarySuchThat`, `EnumSuchThat`)
- [`DeriveChecker.lean`](./Plausible/Chamelean/DeriveChecker.lean): Deriver for automatically deriving checkers (instances of the `DecOpt` typeclass)

**Derivers for unconstrained producers**:
- [`DeriveArbitrary.lean`](./Plausible/DeriveArbitrary.lean): Deriver for unconstrained generators (instances of the `Arbitrary` / `ArbitrarySized` typeclasses)
- [`DeriveEnum.lean`](./Plausible/Chamelean/DeriveEnum.lean): Deriver for unconstrainted enumerators 
(instances of the `Enum` / `EnumSized` typeclasses) 

**Miscellany**:
- [`TSyntaxCombinators.lean`](./Plausible/Chamelean/TSyntaxCombinators.lean): Combinators over `TSyntax` for creating monadic `do`-blocks & other Lean expressions via metaprogramming
- [`LazyList.lean`](./Plausible/Chamelean/LazyList.lean): Implementation of lazy lists (used for enumerators)
- [`Idents.lean`](./Plausible/Chamelean/Idents.lean): Utilities for dealing with identifiers / producing fresh names 
- [`Utils.lean`](./Plausible/Chamelean/Utils.lean): Other miscellaneous utils

**Examples**:
- [`ExampleInductiveRelations.lean`](./Plausible/Chamelean/Examples/ExampleInductiveRelations.lean): Some example inductive relations (BSTs, balanced trees, STLC)
- [`STLC.lean`](./Plausible/Chamelean/Examples/STLC.lean): Example hand-written checkers & generators for well-typed STLC terms
- [`Trees.lean`](./Plausible/Chamelean/Examples/Trees.lean): Example hand-written checkers & generators for balanced trees & BSTs
- [`DeriveRegExpGenerator.lean`](./Test/DeriveArbitrary/DeriveRegExpGenerator.lean): Example generators for regular expressions

**Tests**:      
- The [`Test`](./Test/) subdirectory contains [snapshot tests](https://www.cs.cornell.edu/~asampson/blog/turnt.html) (aka [expect tests](https://blog.janestreet.com/the-joy-of-expect-tests/)) for the `#derive_generator` & `#derive_arbitrary` command elaborators. 
- Run `lake test` to check that the derived generators in [`Test`](./Test/) typecheck, and that the code for the derived generators match the expected output.
- See [`DeriveBSTGenerator.lean`](./Test/DeriveArbitrarySuchThat/DeriveBSTGenerator.lean) & [`DeriveBalancedTreeGenerator.lean`](./Test/DeriveArbitrarySuchThat/DeriveBalancedTreeGenerator.lean) for examples of snapshot tests. Follow the template in these two files to add new snapshot test file, and remember to import the new test file in [`Test.lean`](./Test.lean) afterwards.
