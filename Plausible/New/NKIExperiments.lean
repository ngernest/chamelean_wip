import Plausible.Gen
import Plausible.New.GeneratorCombinators
import Plausible.New.DecOpt
import Plausible.New.GenSizedSuchThat
import Plausible.New.GenSized
import Plausible.New.DeriveGenerator

open GeneratorCombinators


-- inductive SNat (nnat : Nat)
--   | param (idx : Fin nnat)
--   | const (n : Nat)


-- ShapeConstrVal is a parameterized type -- QuickChick only supports Derive Arbitrary for non-parameterized types
inductive ShapeConstrVal (nnat : Nat) where
  | const : Nat → ShapeConstrVal nnat
  | param : Fin nnat → ShapeConstrVal nnat



-- instance : GenSized (ShapeConstrVal nnat) where
--   genSized :=
--     let rec aux_arb (initSize : Nat) (size : Nat) : Plausible.Gen (ShapeConstrVal nnat) :=
--       match size with
--       | Nat.zero =>
--         frequency ()
--           [(1,
--               thunkGen
--                 (fun _ => do
--                   let nnat ← Plausible.SampleableExt.interpSample Nat
--                   return nnat)),
--             (1,
--               thunkGen
--                 (fun _ => do
--                   let nnat ← Plausible.SampleableExt.interpSample Nat
--                   return nnat))]
--       | Nat.succ size' =>
--         frequency _
--           [(1,
--               thunkGen
--                 (fun _ => do
--                   let nnat ← Plausible.SampleableExt.interpSample Nat
--                   return nnat)),
--             (1,
--               thunkGen
--                 (fun _ => do
--                   let nnat ← Plausible.SampleableExt.interpSample Nat
--                   return nnat))]
--     fun size => aux_arb size size
