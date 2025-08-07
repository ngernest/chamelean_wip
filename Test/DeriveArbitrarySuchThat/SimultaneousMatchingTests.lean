
import Plausible.Gen
import Plausible.New.OptionTGen
import Plausible.New.DecOpt
import Plausible.New.ArbitrarySizedSuchThat
import Plausible.GeneratingGoodGenerators.DeriveScheduledGenerator
import Plausible.New.DeriveChecker
import Test.CommonDefinitions.ListRelations
import Test.DeriveDecOpt.SimultaneousMatchingTests

open ArbitrarySizedSuchThat OptionTGen

set_option guard_msgs.diff true


/--
info: Try this generator: instance : ArbitrarySizedSuchThat (List Nat) (fun l_1 => InList x_1 l_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (x_1 : Nat) : OptionT Plausible.Gen (List Nat) :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1, do
              let l ← Arbitrary.arbitrary;
              return List.cons x_1 l)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1, do
              let l ← Arbitrary.arbitrary;
              return List.cons x_1 l),
            (Nat.succ size', do
              let l ← aux_arb initSize size' x_1;
              do
                let y ← Arbitrary.arbitrary;
                return List.cons y l)]
    fun size => aux_arb size size x_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (l : List Nat) => InList x l)


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
#derive_generator (fun (l: List Nat) => MinOk l a)

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
#derive_generator (fun (l : List Nat) => MinEx n l l')

-- Dummy `ArbitrarySizedSuchThat` instance needed so that the derived generator below compiles
instance : ArbitrarySizedSuchThat (List Nat) (fun (l : List Nat) => l = [x] ++ l') where
  arbitrarySizedST (_size : Nat) := return [x] ++ l'

/--
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
            (1, do
              let l_1 ← Arbitrary.arbitrary;
              do
                let l'_1 ←
                  ArbitrarySizedSuchThat.arbitrarySizedST
                      (fun l'_1 => Eq l'_1 (HAppend.hAppend (List.cons x_1 (List.nil)) l_1)) initSize;
                return l_1)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              match l'_1 with
              | List.nil =>
                match x_1 with
                | Nat.zero => return List.nil
                | _ => OptionT.fail
              | _ => OptionT.fail),
            (1, do
              let l_1 ← Arbitrary.arbitrary;
              do
                let l'_1 ←
                  ArbitrarySizedSuchThat.arbitrarySizedST
                      (fun l'_1 => Eq l'_1 (HAppend.hAppend (List.cons x_1 (List.nil)) l_1)) initSize;
                return l_1),
            ]
    fun size => aux_arb size size x_1 l'_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (l : List Nat) => MinEx3 x l l')

/--
info: Try this generator: instance : ArbitrarySizedSuchThat (List Nat) (fun l'_1 => MinEx2 x_1 l_1 l'_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (x_1 : Nat) (l_1 : List Nat) : OptionT Plausible.Gen (List Nat) :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              match l_1 with
              | List.nil =>
                match x_1 with
                | Nat.zero => return List.nil
                | _ => OptionT.fail
              | _ => OptionT.fail)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              match l_1 with
              | List.nil =>
                match x_1 with
                | Nat.zero => return List.nil
                | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match x_1 with
              | Nat.succ x => do
                let l' ← aux_arb initSize size' x l_1;
                do
                  let l'_1 ←
                    ArbitrarySizedSuchThat.arbitrarySizedST
                        (fun l'_1 => Eq l'_1 (HAppend.hAppend (List.cons x (List.nil)) l')) initSize;
                  return l'_1
              | _ => OptionT.fail)]
    fun size => aux_arb size size x_1 l_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (l' : List Nat) => MinEx2 x l l')

/--
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
              match x_1 with
              | Nat.succ x => do
                let l_1 ← Arbitrary.arbitrary;
                do
                  let l' ← ArbitrarySizedSuchThat.arbitrarySizedST (fun l' => MinEx2 x l_1 l') initSize;
                  do
                    let l'_1 ←
                      ArbitrarySizedSuchThat.arbitrarySizedST
                          (fun l'_1 => Eq l'_1 (HAppend.hAppend (List.cons x (List.nil)) l')) initSize;
                    return l_1
              | _ => OptionT.fail)]
    fun size => aux_arb size size x_1 l'_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (l : List Nat) => MinEx2 x l l')
