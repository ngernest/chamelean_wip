import Plausible.IR.Examples
import Plausible.New.OptionTGen
import Plausible.New.ArbitrarySizedSuchThat
import Plausible.New.DecOpt
import Plausible.New.GenProofTactics
import Plausible.New.OptionTGenTheorems
import Lean
import Plausible.Gen
import Test.DeriveArbitrary.DeriveRegExpGenerator
open Plausible
open OptionTGen

open ArbitrarySizedSuchThat
open Lean Elab Tactic Meta PrettyPrinter




open ArbitrarySizedSuchThat OptionTGen



/-- `ExpMatch s r` holds if `s` is a string contained in the language defined by `RegExp r`,
    i.e., it "matches" `r` (a string is represented here as a `List Nat`) -/

inductive ExpMatch : List Nat → RegExp → Prop where
| MEmpty : ExpMatch [] RegExp.EmptyStr
| MChar : ∀ x, ExpMatch [x] (RegExp.Char x)
| MApp : ∀ s1 re1 s2 re2,
  ExpMatch s1 re1 →
  ExpMatch s2 re2 →
  ExpMatch (s1 ++ s2) (RegExp.App re1 re2)
| MUnionL : ∀ s1 re1 re2,
  ExpMatch s1 re1 →
  ExpMatch s1 (RegExp.Union re1 re2)
| MUnionR : ∀ re1 s2 re2,
  ExpMatch s2 re2 →
  ExpMatch s2 (RegExp.Union re1 re2)
| MStar0 : ∀ re, ExpMatch [] (RegExp.Star re)
| MStarApp : ∀ s1 s2 re,
  ExpMatch s1 re →
  ExpMatch s2 (RegExp.Star re) →
  ExpMatch (s1 ++ s2) (RegExp.Star re)


-- Creates a string (sequential `App` of `Char`s) -/
def reStr (l : List Nat) (ign : RegExp) : RegExp :=
  match l with
  | [] => ign
  | [x] => RegExp.Char x
  | x :: xs => RegExp.App (RegExp.Char x) (reStr xs ign)

/-- Creates a character class regexp -/
def reCls (l : List Nat) (ign : RegExp) : RegExp :=
  match l with
  | [] => ign
  | [x] => RegExp.Char x
  | x :: xs => RegExp.Union (RegExp.Char x) (reCls xs ign)

/-- reg_exp is `1230*[456]*` -/
def r0 : RegExp :=
  RegExp.App
    (RegExp.App (reStr [1, 2, 3] (RegExp.Char 0)) (RegExp.Star (RegExp.Char 0)))
    (RegExp.Star (reCls [4, 5, 6] (RegExp.Char 0)))

-- Generator for strings that match the regexp `r0`


def gen_RegEx (r0_0 : RegExp) : Nat →  OptionT Plausible.Gen (List Nat) :=
    let rec aux_arb (initSize : Nat) (size : Nat) (r0_0 : RegExp) : OptionT Plausible.Gen (List Nat) :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              OptionTGen.thunkGen
                (fun _ =>
                  match r0_0 with
                  | RegExp.EmptyStr => pure []
                  | _ => OptionT.fail)),
            (1,
              OptionTGen.thunkGen
                (fun _ =>
                  match r0_0 with
                  | RegExp.Char x => pure [x]
                  | _ => OptionT.fail)),
            (1,
              OptionTGen.thunkGen
                (fun _ =>
                  match r0_0 with
                  | RegExp.Star re => pure []
                  | _ => OptionT.fail)),
            (1, OptionTGen.thunkGen (fun _ => OptionT.fail))]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              OptionTGen.thunkGen
                (fun _ =>
                  match r0_0 with
                  | RegExp.EmptyStr => pure []
                  | _ => OptionT.fail)),
            (1,
              OptionTGen.thunkGen
                (fun _ =>
                  match r0_0 with
                  | RegExp.Char x => pure [x]
                  | _ => OptionT.fail)),
            (Nat.succ size',
              OptionTGen.thunkGen
                (fun _ =>
                  match r0_0 with
                  | RegExp.App re1 re2 => do
                    let s1 ← aux_arb initSize size' re1
                    let s2 ← aux_arb initSize size' re2
                    return s1 ++ s2
                  | _ => OptionT.fail)),
            (Nat.succ size',
              OptionTGen.thunkGen
                (fun _ =>
                  match r0_0 with
                  | RegExp.Union re1 re2 => do
                    let s ← aux_arb initSize size' re1
                    return s
                  | _ => OptionT.fail)),
            (Nat.succ size',
              OptionTGen.thunkGen
                (fun _ =>
                  match r0_0 with
                  | RegExp.Union re1 re2 => do
                    let s ← aux_arb initSize size' re2
                    return s
                  | _ => OptionT.fail)),
            (1,
              OptionTGen.thunkGen
                (fun _ =>
                  match r0_0 with
                  | RegExp.Star re => pure []
                  | _ => OptionT.fail)),
            (Nat.succ size',
              OptionTGen.thunkGen
                (fun _ =>
                  match r0_0 with
                  | RegExp.Star re => do
                    let s1 ← aux_arb initSize size' re
                    let s2 ← aux_arb initSize size' (RegExp.Star re)
                    return s1 ++ s2
                  | _ => OptionT.fail))]
    termination_by size
    fun size => aux_arb size size r0_0


theorem genReg_correct: OptionTGenEnsure (fun x => ExpMatch x r) (gen_RegEx r size) := by
  gen_proof




/--
info: Try this generator: instance : ArbitrarySizedSuchThat (List Nat) (fun s => ExpMatch s r0) where
  arbitrarySizedST :=
    let rec aux_arb' (initSize : Nat) (size : Nat) (r0_0 : RegExp) : OptionT Plausible.Gen (List Nat) :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              OptionTGen.thunkGen
                (fun _ =>
                  match r0_0 with
                  | RegExp.EmptyStr => pure []
                  | _ => OptionT.fail)),
            (1,
              OptionTGen.thunkGen
                (fun _ =>
                  match r0_0 with
                  | RegExp.Char x => pure [x]
                  | _ => OptionT.fail)),
            (1,
              OptionTGen.thunkGen
                (fun _ =>
                  match r0_0 with
                  | RegExp.Star re => pure []
                  | _ => OptionT.fail)),
            (1, OptionTGen.thunkGen (fun _ => OptionT.fail))]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              OptionTGen.thunkGen
                (fun _ =>
                  match r0_0 with
                  | RegExp.EmptyStr => pure []
                  | _ => OptionT.fail)),
            (1,
              OptionTGen.thunkGen
                (fun _ =>
                  match r0_0 with
                  | RegExp.Char x => pure [x]
                  | _ => OptionT.fail)),
            (Nat.succ size',
              OptionTGen.thunkGen
                (fun _ =>
                  match r0_0 with
                  | RegExp.App re1 re2 => do
                    let s1 ← aux_arb' initSize size' re1
                    let s2 ← aux_arb' initSize size' re2
                    return s1 ++ s2
                  | _ => OptionT.fail)),
            (Nat.succ size',
              OptionTGen.thunkGen
                (fun _ =>
                  match r0_0 with
                  | RegExp.Union re1 re2 => do
                    let s ← aux_arb' initSize size' re1
                    return s
                  | _ => OptionT.fail)),
            (Nat.succ size',
              OptionTGen.thunkGen
                (fun _ =>
                  match r0_0 with
                  | RegExp.Union re1 re2 => do
                    let s ← aux_arb' initSize size' re2
                    return s
                  | _ => OptionT.fail)),
            (1,
              OptionTGen.thunkGen
                (fun _ =>
                  match r0_0 with
                  | RegExp.Star re => pure []
                  | _ => OptionT.fail)),
            (Nat.succ size',
              OptionTGen.thunkGen
                (fun _ =>
                  match r0_0 with
                  | RegExp.Star re => do
                    let s1 ← aux_arb' initSize size' re
                    let s2 ← aux_arb' initSize size' (RegExp.Star re)
                    return s1 ++ s2
                  | _ => OptionT.fail))]
    fun size => aux_arb' size size r0
-/


-- To sample from this generator, we can run the following:
-- #eval runSizedGen (arbitrarySizedST (fun s => ExpMatch s r0)) 10
