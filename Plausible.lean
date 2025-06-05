/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Plausible.Random
import Plausible.Gen
import Plausible.Sampleable
import Plausible.Testable
import Plausible.Functions
import Plausible.Attr
import Plausible.Tactic

-- TODO: remove these imports in production code
-- (these are here so that `lake build` compiles the new metaprogramming code)
import Plausible.IR.PlausibleIR

import Plausible.New.DeriveChecker
import Plausible.New.DeriveGenerator
import Plausible.New.GenOption
import Plausible.New.Tests
import Plausible.New.OptionTGen
