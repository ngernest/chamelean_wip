import Plausible.New.DecOpt
import Plausible.New.DeriveChecker
import Test.DeriveDecOpt.DeriveBSTChecker
import Test.DeriveArbitrarySuchThat.SimultaneousMatchingTests

open DecOpt

set_option guard_msgs.diff true

/--
info: Try this checker: instance : DecOpt (MinOk l a) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (l_0 : List Nat) (a_0 : List Nat) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match l_0, a_0 with
            | [], [] => Option.some Bool.true
            | _, _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match l_0, a_0 with
            | [], [] => Option.some Bool.true
            | _, _ => Option.some Bool.false,
            fun _ =>
            match a_0 with
            | x :: l' =>
              DecOpt.andOptList
                [DecOpt.decOpt (@Membership.mem Nat (List Nat) List.instMembership l x) initSize,
                  aux_dec initSize size' l l']
            | _ => Option.some Bool.false]
    fun size => aux_dec size size l a
-/
#guard_msgs(info, drop warning) in
#derive_checker (MinOk l a)

/--
info: Try this checker: instance : DecOpt (MinEx n l a) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (n_0 : Nat) (l_0 : List Nat) (a_0 : List Nat) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match n_0, l_0, a_0 with
            | 0, [], [] => Option.some Bool.true
            | _, _, _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match n_0, l_0, a_0 with
            | 0, [], [] => Option.some Bool.true
            | _, _, _ => Option.some Bool.false,
            fun _ =>
            match n_0, a_0 with
            | Nat.succ n_1, x :: l' =>
              DecOpt.andOptList
                [DecOpt.decOpt (@Membership.mem Nat (List Nat) List.instMembership l x) initSize,
                  aux_dec initSize size' n_1 l l']
            | _, _ => Option.some Bool.false]
    fun size => aux_dec size size n l a
-/
#guard_msgs(info, drop warning) in
#derive_checker (MinEx n l a)

-- TODO: test derived checkers on the other examples in `Test.DeriveArbitrarySuchThat.SimultaneousMatchingTests`
