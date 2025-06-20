import Plausible.Gen
import Plausible.New.OptionTGen
import Plausible.New.DecOpt
import Plausible.New.GenSizedSuchThat
import Plausible.New.DeriveGenerator
-- import Plausible.NKI.TypeCheck

-- open Plausible.NKI

inductive ShapeConstrVal (nnat : Nat) where
  | const : Nat → ShapeConstrVal nnat
  | param : Fin nnat → ShapeConstrVal nnat

-- TODO: figure out why `Nat` is being classified as a `Action.checkNonInductive`

-- #derive_generator (fun (nnat : Nat) => ShapeConstrVal nnat)
