import Plausible.New.DecOpt
import Plausible.New.Enumerators
import Plausible.New.DeriveEnumSuchThat
import Plausible.New.EnumeratorCombinators

-- See `Test/DeriveArbitrarySuchThat/SimultaneousMatchingTests.lean` for the definition of the inductive relations
import Test.DeriveArbitrarySuchThat.SimultaneousMatchingTests

set_option guard_msgs.diff true

/--
info: Try this generator: instance : EnumSizedSuchThat (List Nat) (fun l => MinOk l a) where
  enumSizedST :=
    let rec aux_enum (initSize : Nat) (size : Nat) (a_0 : List Nat) : OptionT Enumerator (List Nat) :=
      match size with
      | Nat.zero =>
        EnumeratorCombinators.enumerate
          [match a_0 with
            | [] => pure []
            | _ => OptionT.fail,
            OptionT.fail]
      | Nat.succ size' =>
        EnumeratorCombinators.enumerate
          [match a_0 with
            | [] => pure []
            | _ => OptionT.fail,
            match a_0 with
            | x :: l' => do
              let l ← aux_enum initSize size' l'
              if x ∈ l then ⏎
                return l
              else
                OptionT.fail
            | _ => OptionT.fail]
    fun size => aux_enum size size a
-/
#guard_msgs(info, drop warning) in
#derive_enumerator (fun (l: List Nat) => MinOk l a)

/--
info: Try this generator: instance : EnumSizedSuchThat (List Nat) (fun l => MinEx n l a) where
  enumSizedST :=
    let rec aux_enum (initSize : Nat) (size : Nat) (n_0 : Nat) (a_0 : List Nat) : OptionT Enumerator (List Nat) :=
      match size with
      | Nat.zero =>
        EnumeratorCombinators.enumerate
          [match n_0, a_0 with
            | 0, [] => pure []
            | _, _ => OptionT.fail,
            OptionT.fail]
      | Nat.succ size' =>
        EnumeratorCombinators.enumerate
          [match n_0, a_0 with
            | 0, [] => pure []
            | _, _ => OptionT.fail,
            match n_0, a_0 with
            | Nat.succ n, x :: l' => do
              let l ← aux_enum initSize size' n l'
              if x ∈ l then ⏎
                return l
              else
                OptionT.fail
            | _, _ => OptionT.fail]
    fun size => aux_enum size size n a
-/
#guard_msgs(info, drop warning) in
#derive_enumerator (fun (l: List Nat) => MinEx n l a)
