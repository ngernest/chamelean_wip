-- import Plausible.New.DeriveGenerator

-- inductive ApiResult where
-- | Ok : ApiResult
-- | Error : String → ApiResult
-- deriving Repr

-- inductive State where
-- | principal : Nat → State
-- deriving Repr, DecidableEq

-- instance : Plausible.Shrinkable State where
--   shrink := fun ⟨ x ⟩ =>
--     let proxy := Plausible.Shrinkable.shrink x
--     proxy.map (fun x => ⟨ x ⟩ )

-- instance : Plausible.SampleableExt State :=
--   Plausible.SampleableExt.mkSelfContained do
--     let x ← Plausible.SampleableExt.interpSample Nat
--     return ⟨ x ⟩

-- inductive LookupResult where
-- | None : LookupResult
-- | Found : State → LookupResult
-- deriving Repr

-- inductive LookupState : State → (List State) → LookupResult → Prop where
-- | L_none : ∀ k, LookupState k [] .None
-- | L_found : ∀ k l, LookupState k (k::l) (.Found k)
-- | L_cons : ∀ k h t r, k != h → LookupState k t r → LookupState k (h::t) r

-- #derive_generator (fun (l: List State) => LookupState s l r)
