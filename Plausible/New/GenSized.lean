import Plausible.Gen
import Plausible.New.GeneratorCombinators
import Plausible.Sampleable

open Plausible

/-- This is the equivalent of Haskell QuickCheck's `Arbitrary` typeclass.
    (In QuickChick, this typeclass is called `Gen`, but `Gen` is already
    a reserved keyword in Plausible, so we call this typeclass `Arbitrary`
    following the Haskell QC convention) -/
class Arbitrary (α : Type) where
  gen : Gen α

/-- Equivalent to QuickChick's `GenSized` typeclass -/
class ArbitrarySized (α : Type) where
  genSized : Nat → Gen α

/-- Every `GenSized` instance gives rise to a `SampleableExt` instance
    - Note: Plausible's `SampleableExt` is analogous to QuickChick's `Arbitrary` typeclass
      (which combines QuickChick's `Gen` and `Shrink` typeclass)-/
instance [Repr α] [Shrinkable α] [ArbitrarySized α] : SampleableExt α :=
  SampleableExt.mkSelfContained (GeneratorCombinators.sized ArbitrarySized.genSized)

-- TODO: figure out how to distinguish between `GenSized` and `GenSizedSuchThat` in Chamelean

-- TODO: just try to implement `Derive` for ordinary types???
