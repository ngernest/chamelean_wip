
import Lean
import Std
import Plausible.IR.Example
import Plausible.IR.Extractor
import Plausible.IR.Prelude
import Plausible.IR.Prototype
import Plausible.IR.GCCall
import Plausible.IR.Constructor
import Plausible.Gen
import Plausible.Sampleable
import Lean.Elab.Deriving.DecEq
open List Nat Array String
open Lean Elab Command Meta Term
open Lean.Parser.Term
open Plausible Gen

namespace Plausible.IR

-- Generate backtrack list --

def size_zero_backtrack_for_checker (r: IR_info): MetaM (Array String) := do
  let mut i := 0
  let mut out : Array String := #[]
  for ctor in r.constructors do
    i := i + 1
    if ctor.recursive_hypotheses.size = 0 then
      let bt := "check_" ++ afterLastDot r.name.toString ++"_by_con_" ++ toString i
      out:= out.push bt
  return out

def size_pos_backtrack_for_checker (r: IR_info): MetaM (Array String) := do
  let mut i := 0
  let mut out : Array String := #[]
  for con in r.constructors do
    i := i + 1
    if con.recursive_hypotheses.size > 0 then
      let bt := "check_" ++ afterLastDot r.name.toString ++"_by_con_" ++ toString i
      out:= out.push bt
  return out

def size_zero_backtrack_for_producer (r: IR_info) (genpos: Nat): MetaM (Array String) := do
  let mut i := 0
  let mut out : Array String := #[]
  for con in r.constructors do
    i := i + 1
    if con.recursive_hypotheses.size = 0 then
      let bt := "gen_" ++ afterLastDot r.name.toString ++ "_at_" ++ toString genpos  ++"_by_con_" ++ toString i
      out:= out.push bt
  return out

def size_pos_backtrack_for_producer (r: IR_info) (genpos: Nat): MetaM (Array String) := do
  let mut i := 0
  let mut out : Array String := #[]
  for con in r.constructors do
    i := i + 1
    if con.recursive_hypotheses.size > 0 then
      let bt := "gen_" ++ afterLastDot r.name.toString ++ "_at_" ++ toString genpos ++"_by_con_" ++ toString i
      out:= out.push bt
  return out

def uniform_backtrack_codeblock (btarray: Array String) (inps: List String) (backtracknum: Nat)
      (monad: String :="IO") : MetaM String := do
  let mut body := " for _i in [1:" ++ toString backtracknum ++ "] do\n"
  body:= body ++ "  let f ← uniform_backtracking_" ++ monad ++ " #["
  for bt in btarray do
    body := body ++ bt ++ ", "
  body:= ⟨body.data.dropLast.dropLast⟩ ++ "] "
  body:= body ++ "\n  let ret ← "
  body:= if monad = "IO" then body ++ monad ++ "_to_option (f size " else body ++ "(f size "
  for i in inps do
    body:= body ++ i ++ " "
  body:= ⟨body.data.dropLast⟩ ++ ")\n"
  body:= body ++ "  match ret with\n"
  body:= body ++ "  | some ret => return ret\n"
  body:= body ++ "  | _ => continue\n"
  let monad_fail: String := if monad = "IO" then "throw (IO.userError \"fail\")" else "return false"
  body:= body ++ " " ++ monad_fail
  return body

def weight_backtrack_codeblock (btarray: Array String) (inps: List String) (backtracknum: Nat) (low_weight_size: Nat)
    (monad: String :="IO") : MetaM String := do
  let mut body := " for _i in [1:" ++ toString backtracknum ++ "] do\n"
  body:= body ++ "  let f ← weight_backtracking_" ++ monad ++ " #["
  for bt in btarray do
    body := body ++ bt ++ ", "
  body:= ⟨body.data.dropLast.dropLast⟩ ++ "] " ++ toString low_weight_size ++ " size"
  body:= body ++ "\n  let ret ← "
  body:= if monad = "IO" then body ++ monad ++ "_to_option (f size " else body ++ "(f size "
  for i in inps do
    body:= body ++ i ++ " "
  body:= ⟨body.data.dropLast⟩ ++ ")\n"
  body:= body ++ "  match ret with\n"
  body:= body ++ "  | some ret => return ret\n"
  body:= body ++ "  | _ => continue\n"
  let monad_fail: String := if monad = "IO" then "throw (IO.userError \"fail\")" else "return false"
  body:= body ++ " " ++ monad_fail
  return body

def checker_body (r: IR_info) (inpname: List String) (backtracknum: Nat)
    (monad: String :="IO") : MetaM (String) := do
  let mut body := "match size with \n| zero => \n"
  let bt0 ← size_zero_backtrack_for_checker r
  let btblock ← uniform_backtrack_codeblock bt0 inpname backtracknum monad
  body := body ++ btblock
  body:= body ++ "\n| succ size => \n"
  let btpos ← size_pos_backtrack_for_checker r
  let bts:= bt0.append btpos
  let btblock ← weight_backtrack_codeblock bts inpname backtracknum bt0.size monad
  body := body ++ btblock
  return body


def producer_body (r: IR_info) (inpname: List String) (genpos: Nat) (backtracknum: Nat)
    (monad: String :="IO") : MetaM (String) := do
  let mut body := "match size with \n| zero => \n"
  let inps := inpname.take genpos ++ inpname.drop (genpos + 1)
  let bt0 ← size_zero_backtrack_for_producer r genpos
  let btblock ← uniform_backtrack_codeblock bt0 inps backtracknum monad
  body := body ++ btblock
  body:= body ++ "\n| succ size => \n"
  let btpos ← size_pos_backtrack_for_producer r genpos
  let bts:= bt0.append btpos
  let btblock ← weight_backtrack_codeblock bts inps backtracknum bt0.size monad
  body := body ++ btblock
  return body

def MetaM_to_option (m : MetaM α) : MetaM (Option α) := do
  try
    let result ← m
    pure (some result)
  catch _ =>
    pure none

def IO_to_option (io : IO α) : IO (Option α) := do
  try
    let result ← io
    pure (some result)
  catch _ =>
    pure none

def uniform_backtracking_IO {α : Type } (a : Array α) : IO α := do
  -- Using monadLift to lift the random number generation from IO to MetaM
  let idx ← monadLift <| IO.rand 0 (a.size - 1)
  let mem ←  option_to_IO (a[idx]?)
  return mem


def weight_backtracking_IO {α : Type } (a : Array α) (low_weight_size: Nat) (weight: Nat): IO α := do
  -- Using monadLift to lift the random number generation from IO to MetaM
  let maxnum := low_weight_size + (a.size - low_weight_size) * weight - 1
  let randnat ← monadLift <| IO.rand 0 maxnum
  let idx := if randnat < low_weight_size then randnat else (randnat - low_weight_size)/weight + low_weight_size
  let mem ←  option_to_IO (a[idx]?)
  return mem

def uniform_backtracking_Gen {α : Type } (a : Array α) (h: a.size > 0): Gen α := do
  let idx ← choose Nat 0 (a.size -1) (by omega)
  let mem :=  a[idx.val]'(by omega)
  return mem



def weight_backtracking_Gen {α : Type } (a : Array α) (low_weight_size: Nat) (weight: Nat)
      (h1: a.size ≥ low_weight_size  )(h: low_weight_size  > 0): Gen α := do
  let maxnum := low_weight_size + (a.size - low_weight_size)*weight -1
  let randnat ← choose Nat 0 maxnum (by omega)
  let idx := if randnat.val < low_weight_size then randnat.val else (randnat.val - low_weight_size)/weight + low_weight_size
  have h: idx < a.size :=by
    simp only [idx]; split ; omega
    apply Nat.add_lt_of_lt_sub; apply Nat.div_lt_of_lt_mul; apply Nat.sub_lt_left_of_lt_add (by omega)
    have: low_weight_size + weight * (a.size - low_weight_size) = maxnum + 1 :=by rw[Nat.mul_comm] ;omega
    omega
  let mem :=  a[idx]'h
  return mem


--SIMPLE RANDOM GEN
def gen_rand_Nat (min : Nat := 0) (max : Nat := 100) : MetaM Nat := do
  -- Ensure max is greater than or equal to min
  let effectiveMax := if max < min then min else max
  -- Using monadLift to lift IO.rand into MetaM
  monadLift <| IO.rand min effectiveMax

-- Variations with different constraints
def randomNatPositive : MetaM Nat := do
  let n ← gen_rand_Nat 1 100
  return n

end Plausible.IR
