import Plausible.New.DecOpt
import Plausible.New.Enumerators
import Plausible.New.DeriveEnumSuchThat
import Plausible.New.EnumeratorCombinators

-- See `Test/CommonDefinitions/ListRelations.lean` for the definition of the inductive relations
import Test.CommonDefinitions.ListRelations

set_option guard_msgs.diff true

/--
info: Try this enumerator: instance : EnumSizedSuchThat (List Nat) (fun l => MinOk l a) where
  enumSizedST :=
    let rec aux_enum (initSize : Nat) (size : Nat) (a_1 : List Nat) : OptionT Enumerator (List Nat) :=
      match size with
      | Nat.zero =>
        EnumeratorCombinators.enumerate
          [match a_1 with
            | [] => pure []
            | _ => OptionT.fail,
            OptionT.fail]
      | Nat.succ size' =>
        EnumeratorCombinators.enumerate
          [match a_1 with
            | [] => pure []
            | _ => OptionT.fail,
            match a_1 with
            | x :: l' => do
              let l_1 ← aux_enum initSize size' l'
              return l_1
            | _ => OptionT.fail]
    fun size => aux_enum size size a
-/
#guard_msgs(info, drop warning) in
#derive_enumerator (fun (l: List Nat) => MinOk l a)

/--
info: Try this enumerator: instance : EnumSizedSuchThat (List Nat) (fun l => MinEx n l a) where
  enumSizedST :=
    let rec aux_enum (initSize : Nat) (size : Nat) (n_1 : Nat) (a_1 : List Nat) : OptionT Enumerator (List Nat) :=
      match size with
      | Nat.zero =>
        EnumeratorCombinators.enumerate
          [match n_1, a_1 with
            | Nat.zero, [] => pure []
            | _, _ => OptionT.fail,
            OptionT.fail]
      | Nat.succ size' =>
        EnumeratorCombinators.enumerate
          [match n_1, a_1 with
            | Nat.zero, [] => pure []
            | _, _ => OptionT.fail,
            match n_1, a_1 with
            | Nat.succ n, x :: l' => do
              let l_1 ← aux_enum initSize size' n l'
              return l_1
            | _, _ => OptionT.fail]
    fun size => aux_enum size size n a
-/
#guard_msgs(info, drop warning) in
#derive_enumerator (fun (l: List Nat) => MinEx n l a)
