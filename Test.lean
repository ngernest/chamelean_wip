/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
-- import Test.Tactic
-- import Test.Testable

-- Tests for `#derive_generator` (`derives ArbitrarySuchThat`)
import Test.DeriveArbitrarySuchThat.DeriveBSTGenerator
import Test.DeriveArbitrarySuchThat.DeriveBalancedTreeGenerator
import Test.DeriveArbitrarySuchThat.DeriveRegExpMatchGenerator
import Test.DeriveArbitrarySuchThat.DeriveSTLCGenerator
import Test.DeriveArbitrarySuchThat.SimultaneousMatchingTests
import Test.DeriveArbitrarySuchThat.NonLinearPatternsTest

-- Tests for `deriving Arbitrary`
import Test.DeriveArbitrary.DeriveTreeGenerator
import Test.DeriveArbitrary.DeriveSTLCTermTypeGenerators
import Test.DeriveArbitrary.DeriveNKIValueGenerator
import Test.DeriveArbitrary.DeriveNKIBinopGenerator
import Test.DeriveArbitrary.DeriveRegExpGenerator
import Test.DeriveArbitrary.StructureTest
import Test.DeriveArbitrary.BitVecStructureTest

-- Tests for instances of `Enum` for simple types
import Test.Enum.EnumInstancesTest

-- Tests for `deriving Enum`
import Test.DeriveEnum.DeriveTreeEnumerator
import Test.DeriveEnum.DeriveSTLCTermTypeEnumerators
import Test.DeriveEnum.DeriveNKIValueEnumerator
import Test.DeriveEnum.DeriveNKIBinopEnumerator
import Test.DeriveEnum.DeriveRegExpEnumerator
import Test.DeriveEnum.StructureTest
import Test.DeriveEnum.BitVecStructureTest
