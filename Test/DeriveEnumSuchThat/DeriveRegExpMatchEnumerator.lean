import Plausible.New.DecOpt
import Plausible.New.Enumerators
import Plausible.New.DeriveEnumSuchThat
import Plausible.New.EnumeratorCombinators
import Test.DeriveArbitrarySuchThat.DeriveRegExpMatchGenerator

set_option guard_msgs.diff true

/--
info: Try this generator: instance : EnumSizedSuchThat (List Nat) (fun s => ExpMatch s r0) where
  enumSizedST :=
    let rec aux_enum (initSize : Nat) (size : Nat) (r0_0 : RegExp) : OptionT Enumerator (List Nat) :=
      match size with
      | Nat.zero =>
        EnumeratorCombinators.enumerate
          [match r0_0 with
            | RegExp.EmptyStr => pure []
            | _ => OptionT.fail,
            match r0_0 with
            | RegExp.Char x => pure [x]
            | _ => OptionT.fail,
            match r0_0 with
            | RegExp.Star re => pure []
            | _ => OptionT.fail,
            OptionT.fail]
      | Nat.succ size' =>
        EnumeratorCombinators.enumerate
          [match r0_0 with
            | RegExp.EmptyStr => pure []
            | _ => OptionT.fail,
            match r0_0 with
            | RegExp.Char x => pure [x]
            | _ => OptionT.fail,
            match r0_0 with
            | RegExp.App re1 re2 => do
              let s1 ← aux_enum initSize size' re1
              let s2 ← aux_enum initSize size' re2
              return s1 ++ s2
            | _ => OptionT.fail,
            match r0_0 with
            | RegExp.Union re1 re2 => do
              let s ← aux_enum initSize size' re1
              return s
            | _ => OptionT.fail,
            match r0_0 with
            | RegExp.Union re1 re2 => do
              let s ← aux_enum initSize size' re2
              return s
            | _ => OptionT.fail,
            match r0_0 with
            | RegExp.Star re => pure []
            | _ => OptionT.fail,
            match r0_0 with
            | RegExp.Star re => do
              let s1 ← aux_enum initSize size' re
              let s2 ← aux_enum initSize size' (RegExp.Star re)
              return s1 ++ s2
            | _ => OptionT.fail]
    fun size => aux_enum size size r0
-/
#guard_msgs(info, drop warning) in
#derive_enumerator (fun (s : List Nat) => ExpMatch s r0)

-- To sample from this enumerator, we can run the following:
-- #eval runSizedEnum (EnumSizedSuchThat.enumSizedST (fun s => ExpMatch s r0)) 3
