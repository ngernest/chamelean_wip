
import Plausible.Gen
import Plausible.New.OptionTGen
import Plausible.New.DecOpt
import Plausible.New.ArbitrarySizedSuchThat
import Plausible.GeneratingGoodGenerators.DeriveSubGenerator
import Plausible.New.DeriveChecker
import Test.CommonDefinitions.ListRelations
import Test.DeriveDecOpt.SimultaneousMatchingTests

open ArbitrarySizedSuchThat OptionTGen

set_option guard_msgs.diff true

/--
info: Try this checker: instance : DecOpt (InList x l) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (x_1 : Nat) (l_1 : List Nat) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match l_1 with
            | x_1_0 :: l => Option.some Bool.true
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match l_1 with
            | x_1_0 :: l => Option.some Bool.true
            | _ => Option.some Bool.false,
            fun _ =>
            match l_1 with
            | y :: l => aux_dec initSize size' x_1 l
            | _ => Option.some Bool.false]
    fun size => aux_dec size size x l
-/
#guard_msgs(info, drop warning) in
#derive_checker (InList x l)


-- TODO: replace this dummy instance with the call `#derive_scheduled_generator (fun (l : List Nat) => InList x l)`
-- after the deriver has been updated to support types which involve type constructor applications (e.g. `List Nat`)
instance : ArbitrarySizedSuchThat (List Nat) (fun l => InList x l) where
  arbitrarySizedST := sorry


-- #guard_msgs(info, drop warning) in
-- #derive_scheduled_generator (fun (l : List Nat) => InList x l)


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
                match DecOpt.decOpt (InList x l_1) initSize with
                  | Option.some Bool.true => return l_1
                  | _ => OptionT.fail
              | _ => OptionT.fail)]
    fun size => aux_arb size size a_1
-/
#guard_msgs(info, drop warning) in
#derive_scheduled_generator (fun (l: List Nat) => MinOk l a)

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
                  let l_1 ← ArbitrarySizedSuchThat.arbitrarySizedST (fun l_1 => InList x l_1) initSize;
                  match DecOpt.decOpt (MinEx n l_1 l') initSize with
                    | Option.some Bool.true => return l_1
                    | _ => OptionT.fail
                | _ => OptionT.fail
              | _ => OptionT.fail)]
    fun size => aux_arb size size n_1 l'_1
-/
#guard_msgs(info, drop warning) in
#derive_scheduled_generator (fun (l : List Nat) => MinEx n l l')


-- TODO: uncomment these failing test after we support rewriting function calls
/-
info: Try this generator: instance : ArbitrarySizedSuchThat (List Nat) (fun l_1 => MinEx2 x_1 l_1 l'_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (x_1 : Nat) (l'_1 : List Nat) : OptionT Plausible.Gen (List Nat) :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              match l'_1 with
              | List.nil =>
                match x_1 with
                | Nat.zero => return List.nil
                | _ => OptionT.fail
              | _ => OptionT.fail)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              match l'_1 with
              | List.nil =>
                match x_1 with
                | Nat.zero => return List.nil
                | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match l'_1 with
              | HAppend.hAppend (List.cons u_3 (List.nil)) l' =>
                match x_1 with
                | Nat.succ x =>
                  match DecOpt.decOpt (BEq.beq u_3 x) initSize with
                  | Option.some Bool.true => do
                    let l_1 ← aux_arb initSize size' x l';
                    return l_1
                  | _ => OptionT.fail
                | _ => OptionT.fail
              | _ => OptionT.fail)]
    fun size => aux_arb size size x_1 l'_1
-/
-- #guard_msgs(info, drop warning) in
-- #derive_scheduled_generator (fun (l : List Nat) => MinEx2 x l l')

/-
info: Try this generator: instance : ArbitrarySizedSuchThat (List Nat) (fun l_1 => MinEx3 x_1 l_1 l'_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (x_1 : Nat) (l'_1 : List Nat) : OptionT Plausible.Gen (List Nat) :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              match l'_1 with
              | List.nil =>
                match x_1 with
                | Nat.zero => return List.nil
                | _ => OptionT.fail
              | _ => OptionT.fail),
            (1,
              match l'_1 with
              | HAppend.hAppend (List.cons u_3 (List.nil)) l_1 =>
                match DecOpt.decOpt (BEq.beq u_3 x_1) initSize with
                | Option.some Bool.true => return l_1
                | _ => OptionT.fail
              | _ => OptionT.fail)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              match l'_1 with
              | List.nil =>
                match x_1 with
                | Nat.zero => return List.nil
                | _ => OptionT.fail
              | _ => OptionT.fail),
            (1,
              match l'_1 with
              | HAppend.hAppend (List.cons u_3 (List.nil)) l_1 =>
                match DecOpt.decOpt (BEq.beq u_3 x_1) initSize with
                | Option.some Bool.true => return l_1
                | _ => OptionT.fail
              | _ => OptionT.fail),
            ]
    fun size => aux_arb size size x_1 l'_1
-/
-- #guard_msgs(info, drop warning) in
-- #derive_scheduled_generator (fun (l : List Nat) => MinEx3 x l l')
