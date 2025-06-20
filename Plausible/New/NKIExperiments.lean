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

-- instance : GenSizedSuchThat Nat (fun nnat => ShapeConstrVal nnat) where
--   genSizedST :=
--     let rec aux_arb (initSize : Nat) (size : Nat) : OptionT Plausible.Gen Nat :=
--       match size with
--       | Nat.zero =>
--         OptionTGen.backtrack
--           [(1,
--               OptionTGen.thunkGen
--                 (fun _ => do
--                   let nnat ← Plausible.SampleableExt.interpSample Nat
--                   return nnat)),
--             (1,
--               OptionTGen.thunkGen
--                 (fun _ => do
--                   let nnat ← Plausible.SampleableExt.interpSample Nat
--                   return nnat)),
--             (1, OptionTGen.thunkGen (fun _ => OptionT.fail))]
--       | Nat.succ size' =>
--         OptionTGen.backtrack
--           [(1,
--               OptionTGen.thunkGen
--                 (fun _ => do
--                   let nnat ← Plausible.SampleableExt.interpSample Nat
--                   return nnat)),
--             (1,
--               OptionTGen.thunkGen
--                 (fun _ => do
--                   let nnat ← Plausible.SampleableExt.interpSample Nat
--                   return nnat))]
--     fun size => aux_arb size size
