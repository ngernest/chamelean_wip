
import Plausible.Gen
import Plausible.New.OptionTGen
import Plausible.New.DecOpt
import Plausible.New.ArbitrarySizedSuchThat
import Plausible.GeneratingGoodGenerators.DeriveSubGenerator

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
info: Try this generator: instance : ArbitrarySizedSuchThat (List Nat) (fun l_1 => MinOk l_1 a_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (a_1 : List Nat) : OptionT Plausible.Gen (List Nat) :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              match a_1 with
              | List.nil => return List.nil
              | _ => OptionT.fail)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              match a_1 with
              | List.nil => return List.nil
              | _ => OptionT.fail),
            (Nat.succ size',
              match a_1 with
              | List.cons x l' => do
                let l_1 ← aux_arb initSize size' l';
                match DecOpt.decOpt (Membership.mem l_1 x) initSize with
                  | Option.some Bool.true => return l_1
                  | _ => OptionT.fail
              | _ => OptionT.fail)]
    fun size => aux_arb size size a_1
-/
#guard_msgs(info, drop warning) in
#derive_scheduled_generator (fun (l: List Nat) => MinOk l a)

/-- Example inductive relation involving simultaneous pattern-matching on multiple inputs -/
inductive MinEx : Nat → List Nat → List Nat → Prop where
| ME_empty : MinEx .zero [] []
| ME_present : ∀ x l n l',
    MinEx n l l' →
    x ∈ l →
    MinEx (Nat.succ n) l (x::l')

/--
info: Try this generator: instance : ArbitrarySizedSuchThat (List Nat) (fun l_1 => MinEx n_1 l_1 l'_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (n_1 : Nat) (l'_1 : List Nat) : OptionT Plausible.Gen (List Nat) :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              match l'_1 with
              | List.nil =>
                match n_1 with
                | Nat.zero => return List.nil
                | _ => OptionT.fail
              | _ => OptionT.fail)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              match l'_1 with
              | List.nil =>
                match n_1 with
                | Nat.zero => return List.nil
                | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match l'_1 with
              | List.cons x l' =>
                match n_1 with
                | Nat.succ n => do
                  let l_1 ← ArbitrarySizedSuchThat.arbitrarySizedST (fun l_1 => Membership.mem l_1 x) initSize;
                  match DecOpt.decOpt (MinEx n l_1 l') initSize with
                    | Option.some Bool.true => return l_1
                    | _ => OptionT.fail
                | _ => OptionT.fail
              | _ => OptionT.fail)]
    fun size => aux_arb size size n_1 l'_1
-/
#guard_msgs(info, drop warning) in
#derive_scheduled_generator (fun (l : List Nat) => MinEx n l l')

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
