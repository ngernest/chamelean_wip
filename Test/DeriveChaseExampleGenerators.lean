
import Plausible.Gen
import Plausible.New.OptionTGen
import Plausible.New.DecOpt
import Plausible.New.GenSizedSuchThat
import Plausible.New.DeriveGenerator

open GenSizedSuchThat OptionTGen

set_option guard_msgs.diff true

/-- Example inductive relation involving pattern-matching on just one input -/
inductive MinOk : List Nat → List Nat → Prop where
| MO_empty : MinOk [] []
| MO_present : ∀ x l l',
    MinOk l l' →
    x ∈ l →
    MinOk l (x::l')

/--
info: Try this generator: instance : GenSizedSuchThat (List Nat) (fun l => MinOk l a) where
  genSizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (a_0 : List Nat) : OptionT Plausible.Gen (List Nat) :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              OptionTGen.thunkGen
                (fun _ =>
                  match a_0 with
                  | [] => pure []
                  | _ => OptionT.fail)),
            (1, OptionTGen.thunkGen (fun _ => OptionT.fail))]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              OptionTGen.thunkGen
                (fun _ =>
                  match a_0 with
                  | [] => pure []
                  | _ => OptionT.fail)),
            (Nat.succ size',
              OptionTGen.thunkGen
                (fun _ =>
                  match a_0 with
                  | x :: l' => do
                    let l ← aux_arb initSize size' l'
                    if x ∈ l then ⏎
                      return l
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
info: Try this generator: instance : GenSizedSuchThat (List Nat) (fun l => MinEx n l a) where
  genSizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (n_0 : Nat) (a_0 : List Nat) : OptionT Plausible.Gen (List Nat) :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              OptionTGen.thunkGen
                (fun _ =>
                  match n_0, a_0 with
                  | 0, [] => pure []
                  | _, _ => OptionT.fail)),
            (1, OptionTGen.thunkGen (fun _ => OptionT.fail))]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              OptionTGen.thunkGen
                (fun _ =>
                  match n_0, a_0 with
                  | 0, [] => pure []
                  | _, _ => OptionT.fail)),
            (Nat.succ size',
              OptionTGen.thunkGen
                (fun _ =>
                  match n_0, a_0 with
                  | Nat.succ n, x :: l' => do
                    let l ← aux_arb initSize size' n l'
                    if x ∈ l then ⏎
                      return l
                    else
                      OptionT.fail
                  | _, _ => OptionT.fail))]
    fun size => aux_arb size size n a
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (l: List Nat) => MinEx n l a)
