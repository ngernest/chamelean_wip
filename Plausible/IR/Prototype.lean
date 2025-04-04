import Lean
import Std
import Plausible.IR.Example
import Plausible.IR.Extractor
import Plausible.IR.Prelude
import Lean.Elab.Deriving.DecEq
import Lean.Meta.Tactic.Simp.Main
open Lean.Elab.Deriving.DecEq
open List Nat Array String
open Lean Elab Command Meta Term
open Lean.Parser.Term

namespace Plausible.IR

-- Generate prototype --
def elim_dot_for_type (name: String) : String :=
  let q := (name.split (fun x => x == ' ')).map afterLastDot
  let qf := q.foldl (fun x y => x ++ " " ++ y) ""
  ⟨qf.data.tail⟩

def prototype_for_checker (r: IR_info) (inpname: List String) : MetaM String := do
  let inps := [("size", Lean.mkConst `Nat)] ++ List.zip inpname r.inp_types.toList
  let genfuncname: String := "check_" ++ afterLastDot r.name.toString
  let mut prototype := "partial def " ++ genfuncname ++ " "
  for inp in inps do
    let name := inp.1
    let type := inp.2
    let typeformat ← Meta.ppExpr type
    let typename := elim_dot_for_type (toString typeformat)
    prototype :=  prototype ++ "(" ++ name ++ " : " ++ typename ++ ") "
  prototype := prototype ++ ": MetaM Bool"
  return prototype

def prototype_for_checker_by_con (r: IR_info) (inpname: List String) (con: Nat): MetaM String := do
  let inps := [("size", Lean.mkConst `Nat)] ++ List.zip inpname r.inp_types.toList
  let genfuncname: String := "check_" ++ afterLastDot r.name.toString ++ "_by_con_" ++ toString con
  let mut prototype := "partial def " ++ genfuncname ++ " "
  for inp in inps do
    let name := inp.1
    let type := inp.2
    let typeformat ← Meta.ppExpr type
    let typename := elim_dot_for_type (toString typeformat)
    prototype :=  prototype ++ "(" ++ name ++ " : " ++ typename ++ ") "
  prototype := prototype ++ ": MetaM Bool"
  return prototype


syntax (name := getcheckerproto) "#get_checker_prototype" term "with_name" term: command

@[command_elab getcheckerproto]
def elabGetprotoChecker : CommandElab := fun stx => do
  match stx with
  | `(#get_checker_prototype $t with_name $t2:term) =>
    Command.liftTermElabM do
      let e ← elabTerm t none
      let relation ←  extract_IR_info e
      let inpname ← termToStringList t2
      let proto := prototype_for_checker relation inpname
      print_m_string proto
  | _ => throwError "Invalid syntax"

#get_checker_prototype typing with_name ["L", "e", "t"]


def prototype_for_producer(r: IR_info) (inpname: List String) (genpos: Nat) : MetaM String := do
  let zipinp := [("size", Lean.mkConst `Nat)] ++ List.zip inpname r.inp_types.toList
  let inps := zipinp.take (genpos + 1) ++ zipinp.drop (genpos + 2)
  let out := zipinp[genpos + 1]!
  let genfuncname: String := "gen_" ++ afterLastDot r.name.toString ++ "_at_" ++ toString genpos
  let mut prototype := "partial def " ++ genfuncname ++ " "
  for inp in inps do
    let name := inp.1
    let type := inp.2
    let typeformat ← Meta.ppExpr type
    let typename := elim_dot_for_type (toString typeformat)
    prototype :=  prototype ++ "(" ++ name ++ " : " ++ typename ++ ") "
  let rettype := elim_dot_for_type (toString (← Meta.ppExpr out.2))
  if rettype.contains ' ' then
    prototype := prototype ++ ": MetaM (" ++ rettype ++ ")"
  else
    prototype := prototype ++ ": MetaM " ++ rettype
  return prototype

def prototype_for_producer_by_con(r: IR_info) (inpname: List String) (genpos: Nat) (con: Nat): MetaM String := do
  let zipinp := [("size", Lean.mkConst `Nat)] ++ List.zip inpname r.inp_types.toList
  let inps := zipinp.take (genpos + 1) ++ zipinp.drop (genpos + 2)
  let out := zipinp[genpos + 1]!
  let genfuncname: String := "gen_" ++ afterLastDot r.name.toString ++ "_at_" ++ toString genpos ++ "_by_con_" ++ toString con
  let mut prototype := "partial def " ++ genfuncname ++ " "
  for inp in inps do
    let name := inp.1
    let type := inp.2
    let typeformat ← Meta.ppExpr type
    let typename := elim_dot_for_type (toString typeformat)
    prototype :=  prototype ++ "(" ++ name ++ " : " ++ typename ++ ") "
  let rettype := elim_dot_for_type (toString (← Meta.ppExpr out.2))
  if rettype.contains ' ' then
    prototype := prototype ++ ": MetaM (" ++ rettype ++ ")"
  else
    prototype := prototype ++ ": MetaM " ++ rettype
  return prototype


syntax (name := getproducerproto) "#get_producer_prototype" term "with_name" term "for_arg" num: command

@[command_elab getproducerproto]
def elabGetprotoProducer : CommandElab := fun stx => do
  match stx with
  | `(#get_producer_prototype $t with_name $t2:term for_arg $t3) =>
    Command.liftTermElabM do
      let e ← elabTerm t none
      let relation ←  extract_IR_info e
      let inpname ← termToStringList t2
      let pos := TSyntax.getNat t3
      let proto := prototype_for_producer relation inpname pos
      print_m_string proto
  | _ => throwError "Invalid syntax"

#get_producer_prototype typing with_name ["L", "e", "t"] for_arg 1

end Plausible.IR
