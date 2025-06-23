import Plausible.New.DeriveGenerator
import Plausible.New.GenSizedSuchThat

inductive MinOk : List Nat → List Nat → Prop where
| MO_empty : MinOk [] []
| MO_present : ∀ x l l',
    MinOk l l' →
    x ∈ l →
    MinOk l (x::l')

-- #derive_generator (fun (l: List Nat) => MinOk l a)

inductive MinEx : Nat → List Nat → List Nat → Prop where
| ME_empty : MinEx 0 [] []
| ME_present : ∀ x l n l',
    MinEx n l l' →
    x ∈ l →
    MinEx (Nat.succ n) l (x::l')

#derive_generator (fun (l: List Nat) => MinEx n l a)
