import Plausible.Gen
import Plausible.New.GeneratorCombinators
import Plausible.Sampleable

open Plausible

/-- This is the equivalent of QuickChick's `Gen` typeclass / Haskell QuickCheck's `Arbitrary` typeclass -/
class GenUnsized (α : Type) where
  gen : Gen α

/-- Equivalent to QuickChick's `GenSized` typeclass -/
class GenSized (α : Type) where
  genSized : Nat → Gen α

/-- Every `GenSized` instance gives rise to a `SampleableExt` instance
    - Note: Plausible's `SampleableExt` is analogous to QuickChick's `Arbitrary` typeclass
      (which combines QuickChick's `Gen` and `Shrink` typeclass)-/
instance [Repr α] [Shrinkable α] [GenSized α] : SampleableExt α :=
  SampleableExt.mkSelfContained (GeneratorCombinators.sized GenSized.genSized)

-- TODO: figure out how to distinguish between `GenSized` and `GenSizedSuchThat` in Chamelean
