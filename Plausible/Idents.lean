/-
Copyright (c) 2025 Ernest Ng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ernest Ng
-/
import Plausible.Gen

import Plausible.Arbitrary
import Plausible.Gen

/-!
# Idents for derived generators

This file defines `Ident`s for commonly-called functions & commonly-referenced types --
these are used in the body of derived generators (when deriving `Arbitrary` instances).

-/

open Lean
open Plausible

namespace Idents

/-- `genFreshName existingNames namePrefix` produces a fresh name with the prefix `namePrefix`
     that is guaranteed to be not within `existingNames`.
    - Note: the body of this function operates in the identity monad since
      we want local mutable state and access to the syntactic sugar
      provided by `while` loops -/
def genFreshName (existingNames : Array Name) (namePrefix : Name) : Name :=
  Id.run do
    let mut count := 0
    let mut freshName := Name.appendAfter namePrefix s!"_{count}"
    while (existingNames.contains freshName) do
      count := count + 1
      freshName := Name.appendAfter namePrefix s!"_{count}"
    return freshName

/-- `genFreshNames existingNames namePrefixes` produces an array of fresh names, all of them
    guaranteed to be not in `existingNames`, where the `i`-th fresh name produced has prefix `namePrefixes[i]`.

    This function is implemented using a fold: when producing the `i`-th fresh name,
    we ensure that it does not clash with `existingNames` *and* the previous `i-1` fresh names produced. -/
def genFreshNames (existingNames : Array Name) (namePrefixes : Array Name) : Array Name :=
  Array.foldl (fun acc name => Array.push acc (genFreshName (acc ++ existingNames) name)) #[] namePrefixes

end Idents
