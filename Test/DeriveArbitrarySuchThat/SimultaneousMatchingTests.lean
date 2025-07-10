
import Plausible.Gen
import Plausible.New.OptionTGen
import Plausible.New.DecOpt
import Plausible.New.ArbitrarySizedSuchThat
import Plausible.New.DeriveArbitrarySuchThat

open ArbitrarySizedSuchThat OptionTGen

set_option guard_msgs.diff true

-- Thanks to Chase Johnson for providing the example inductive relations in this file!

/-- Example inductive relation involving pattern-matching on just one input -/
inductive MinOk : List Nat → List Nat → Prop where
| MO_empty : MinOk [] []
| MO_present : ∀ x l l',
    MinOk l l' →
    x ∈ l →
    MinOk l (x::l')

/--
info: Try this generator: instance : ArbitrarySizedSuchThat (List Nat) (fun l => MinOk l a) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (a_1 : List Nat) : OptionT Plausible.Gen (List Nat) :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              OptionTGen.thunkGen
                (fun _ =>
                  match a_1 with
                  | [] => pure []
                  | _ => OptionT.fail)),
            (1, OptionTGen.thunkGen (fun _ => OptionT.fail))]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              OptionTGen.thunkGen
                (fun _ =>
                  match a_1 with
                  | [] => pure []
                  | _ => OptionT.fail)),
            (Nat.succ size',
              OptionTGen.thunkGen
                (fun _ =>
                  match a_1 with
                  | x :: l' => do
                    let l_1 ← aux_arb initSize size' l'
                    if x ∈ l_1 then ⏎
                      return l_1
                    else
                      OptionT.fail
                  | _ => OptionT.fail))]
    fun size => aux_arb size size a
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (l: List Nat) => MinOk l a)

/-- Example inductive relation involving simultaneous pattern-matching on multiple inputs -/
inductive MinEx : Nat → List Nat → List Nat → Prop where
| ME_empty : MinEx 0 [] []
| ME_present : ∀ x l n l',
    MinEx n l l' →
    x ∈ l →
    MinEx (Nat.succ n) l (x::l')

/--
info: Try this generator: instance : ArbitrarySizedSuchThat (List Nat) (fun l => MinEx n l a) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (n_1 : Nat) (a_1 : List Nat) : OptionT Plausible.Gen (List Nat) :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              OptionTGen.thunkGen
                (fun _ =>
                  match n_1, a_1 with
                  | 0, [] => pure []
                  | _, _ => OptionT.fail)),
            (1, OptionTGen.thunkGen (fun _ => OptionT.fail))]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              OptionTGen.thunkGen
                (fun _ =>
                  match n_1, a_1 with
                  | 0, [] => pure []
                  | _, _ => OptionT.fail)),
            (Nat.succ size',
              OptionTGen.thunkGen
                (fun _ =>
                  match n_1, a_1 with
                  | Nat.succ n, x :: l' => do
                    let l_1 ← aux_arb initSize size' n l'
                    if x ∈ l_1 then ⏎
                      return l_1
                    else
                      OptionT.fail
                  | _, _ => OptionT.fail))]
    fun size => aux_arb size size n a
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (l: List Nat) => MinEx n l a)

-- TODO: test derived generator on this example
-- (need to introduce a fresh variable and an equality constraint between it & the function call
-- (Computing Correctly, section 3.1), i.e. introduce a constraint `l'' = [x] + l'`
inductive MinEx2 : Nat → List Nat → List Nat → Prop where
| ME_empty : MinEx2 0 [] []
| ME_present : ∀ x l l',
    MinEx2 x l l' →
    MinEx2 (Nat.succ x) l ([x] ++ l')


-- TODO: test derived generator on this example
-- (need to support function calls (Computing Correctly section 3.1))
inductive MinEx3 : Nat → List Nat → List Nat → Prop where
| ME_empty : MinEx3 0 [] []
| ME_present : ∀ x l,
    MinEx3 x l ([x] ++ l)
