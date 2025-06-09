import Lean
import Std
import Plausible.IR.Example
import Plausible.IR.Extractor
import Plausible.IR.Prelude
import Plausible.IR.Prototype
import Plausible.IR.GCCall
import Lean.Elab.Deriving.DecEq
open Lean.Elab.Deriving.DecEq
open List Nat Array String
open Lean Elab Command Meta Term
open Lean.Parser.Term


namespace Plausible.IR

-- BACKTRACK CHECKER ---

structure GenCheckCall_group where
  gen_list: Array GenCheckCall
  ifsome_list : Array GenCheckCall
  check_IR_list: Array GenCheckCall
  check_nonIR_list: Array GenCheckCall
  ret : Array GenCheckCall
  variableEqualities : Array (FVarId × FVarId)

structure BacktrackElem where
  inputs : Array String
  inputsToBeMatched : Array String
  exprsToBeMatched : Array Expr
  gcc_group : GenCheckCall_group
  variableEqualities : Array (FVarId × FVarId)


def GenCheckCalls_grouping (gccs: Array GenCheckCall) : MetaM GenCheckCall_group := do
  let mut gen_list : Array GenCheckCall := #[]
  let mut check_IR_list : Array GenCheckCall := #[]
  let mut check_nonIR_list : Array GenCheckCall := #[]
  let mut ifsome_list : Array GenCheckCall := #[]
  let mut ret : Array GenCheckCall := #[]
  let mut var_eq : Array (FVarId × FVarId) := #[]
  for gcc in gccs do
    match gcc with
    | GenCheckCall.gen_fvar _ _
    | GenCheckCall.gen_IR _ _ _ => gen_list := gen_list.push gcc
    | GenCheckCall.mat _ sp =>
      {
        ifsome_list := ifsome_list.push gcc;
        gen_list := gen_list.push gcc;
        var_eq := var_eq ++ sp.eqs;
      }
    | GenCheckCall.ret _ => ret:= ret.push gcc
    | GenCheckCall.check_IR _ => check_IR_list:= check_IR_list.push gcc
    | _ => check_nonIR_list:= check_nonIR_list.push gcc
  return {
    gen_list := gen_list
    check_IR_list := check_IR_list
    check_nonIR_list := check_nonIR_list
    ifsome_list := ifsome_list
    ret:= ret
    variableEqualities := var_eq
  }

def get_checker_backtrack_elem_from_constructor (ctor : InductiveConstructor) (inputNames : List String) : MetaM BacktrackElem := do
  --Get the match expr and inp
  let conclusion ← separate_fvar ctor.conclusion
  let args := (conclusion.cond.getAppArgs).toList
  let inputNamesAndArgs := inputNames.zip args
  let inputPairsThatNeedMatching := inputNamesAndArgs.filter (fun (_, arg) => !arg.isFVar)
  let (inputsToBeMatched, exprsToBeMatched) := inputPairsThatNeedMatching.unzip
  --Get GenCheckCall
  let gccs ← GenCheckCalls_for_checker ctor
  let gcc_group ← GenCheckCalls_grouping gccs
  return {
    inputs := inputNames.toArray
    inputsToBeMatched := inputsToBeMatched.toArray
    exprsToBeMatched := exprsToBeMatched.toArray
    gcc_group := gcc_group
    variableEqualities := conclusion.eqs ++ gcc_group.variableEqualities
  }

def add_size_param (cond: Expr) : MetaM String := do
  let fnname := toString (← Meta.ppExpr cond.getAppFn)
  let arg_str := (toString (← Meta.ppExpr cond)).drop (fnname.length)
  return fnname ++ " size" ++ arg_str

def gen_IR_at_pos_toCode (id: FVarId) (cond: Expr) (pos: Nat) : MetaM String := do
  let new_args := cond.getAppArgs.eraseIdx! pos
  let mut fn_str := "gen_" ++ toString (← Meta.ppExpr cond.getAppFn) ++ "_at_" ++ toString pos ++ " size"
  for a in new_args do
    fn_str := fn_str ++ " "
    if a.getAppArgs.size = 0 then
      fn_str := fn_str ++ toString (← Meta.ppExpr a)
    else
      fn_str := fn_str ++ "(" ++ toString (← Meta.ppExpr a) ++ ")"
  return "let " ++ toString (id.name)  ++ " ← " ++ fn_str

def gen_nonIR_toCode (id: FVarId) (ty: Expr) (monad: String :="IO") : MetaM String := do
  let mut out:= "let "++ toString (id.name)
  let mut typename := afterLastDot (toString (← Meta.ppExpr ty))
  if typename.contains ' ' then typename:= "(" ++ typename ++ ")"
  if monad = "IO" then
    out := out ++ " ← monadLift <| Gen.run (SampleableExt.interpSample " ++ typename ++ ") 100"
  else
    out := out ++ " ←  SampleableExt.interpSample " ++ typename
  return out

def GenCheckCalls_toCode (c: GenCheckCall) (monad: String :="IO"): MetaM (String) := do
  match c with
  | GenCheckCall.check_IR cond => return  "← check_" ++ (← add_size_param cond)
  | GenCheckCall.check_nonIR cond => return  "(" ++ toString (← Meta.ppExpr cond) ++ ")"
  | GenCheckCall.gen_IR id cond pos => gen_IR_at_pos_toCode id cond pos
  | GenCheckCall.mat id sp => return  "if let " ++ toString (← Meta.ppExpr sp.cond) ++ " := " ++ toString (id.name) ++ " then "
  | GenCheckCall.gen_fvar id ty =>  gen_nonIR_toCode id ty monad
  | GenCheckCall.ret e => return "return " ++ (if monad = "IO" then "" else "some ") ++ toString (← Meta.ppExpr e)

def cbe_match_block (cbe: BacktrackElem) : MetaM String := do
  let mut out := ""
  if cbe.inputsToBeMatched.size > 0 then
    out := out ++ "match "
    for i in cbe.inputsToBeMatched do
      out := out ++  i  ++ " , "
    out:= ⟨out.data.dropLast.dropLast⟩ ++ " with \n| "
    for a in cbe.exprsToBeMatched do
      out := out ++ toString (← Meta.ppExpr a) ++ " , "
    out:= ⟨out.data.dropLast.dropLast⟩ ++ " =>  "
  return out

def cbe_gen_block (cbe: BacktrackElem) (monad: String :="IO"): MetaM (String × String) := do
  let mut out := ""
  let mut iden := ""
  for gcc in cbe.gcc_group.gen_list do
    out := out ++ iden ++ (← GenCheckCalls_toCode gcc monad) ++ " \n"
    match gcc with
    | GenCheckCall.mat _ _ => iden := iden ++ " "
    | _ => continue
  if cbe.gcc_group.gen_list.size > 0 then
    out := ⟨out.data.dropLast.dropLast⟩
  return (out, iden)

def cbe_ifsome_block (cbe: BacktrackElem) (monad: String :="IO"): MetaM (String × String) := do
  let mut out := ""
  let iden := if cbe.gcc_group.ifsome_list.size > 0 then "  " else ""
  let mut is_ident:= false
  for gcc in cbe.gcc_group.ifsome_list do
    if is_ident then
      out := out  ++ iden ++ (← GenCheckCalls_toCode gcc monad) ++ " \n"
    else
      out := out  ++ (← GenCheckCalls_toCode gcc monad) ++ " \n"
      is_ident:= true
  if cbe.gcc_group.ifsome_list.size > 0 then
    out := ⟨out.data.dropLast.dropLast⟩
  return (out, iden)

def cbe_gen_check_IR_block (cbe: BacktrackElem) (iden: String) (monad: String :="IO"): MetaM (String × (List String)) := do
  let mut out := ""
  let mut vars : List String := []
  let mut checkcount := 1
  for gcc in cbe.gcc_group.check_IR_list do
    out := out ++ iden ++ "let check" ++ toString checkcount ++ " " ++ (← GenCheckCalls_toCode gcc monad) ++ " \n"
    vars := vars ++ [toString checkcount]
    checkcount := checkcount + 1
  if cbe.gcc_group.check_IR_list.size > 0 then
    out := ⟨out.data.dropLast.dropLast⟩
  return (out, vars)

def cbe_return_checker (cbe: BacktrackElem) (iden: String) (vars: List String) (monad: String :="IO"): MetaM String := do
  let mut out := ""
  if cbe.variableEqualities.size + cbe.gcc_group.check_nonIR_list.size + cbe.gcc_group.check_IR_list.size > 0 then
    out := out ++ iden ++ "return "
  else
    out := out ++ "return true"
  for v in vars do
    out := out ++ "check" ++ v ++ " && "
  for i in cbe.variableEqualities do
    out := out ++  "(" ++ toString (i.1.name) ++ " == " ++ toString (i.2.name) ++ ") && "
  for gcc in cbe.gcc_group.check_nonIR_list do
    out := out ++ (← GenCheckCalls_toCode gcc monad) ++ " && "
  if cbe.variableEqualities.size + cbe.gcc_group.check_nonIR_list.size + cbe.gcc_group.check_IR_list.size > 0 then
    out:= ⟨out.data.dropLast.dropLast.dropLast⟩
  if cbe.gcc_group.ifsome_list.size > 0 then
      out := out ++ "\nreturn false"
  if cbe.inputsToBeMatched.size > 0 then
    out:= out ++ "\n| " ++ makeUnderscores_commas cbe.inputsToBeMatched.size ++ " => return false"
  return out

def backtrack_elem_toString_checker (cbe: BacktrackElem) (monad: String :="IO"): MetaM String := do
  let mut out := ""
  let matchblock ← cbe_match_block cbe
  let (genblock, iden) ← cbe_gen_block cbe monad
  --let (ifsomeblock, iden) ← cbe_ifsome_block cbe monad
  let (checkIRblock, vars) ← cbe_gen_check_IR_block cbe iden monad
  let returnblock ← cbe_return_checker cbe iden vars monad
  out := out ++ matchblock
  --if genblock.length + ifsomeblock.length + checkIRblock.length + returnblock.length > 0 ∧ out.length > 0 then
  if genblock.length > 0 ∧ out.length > 0 then
    out := out ++ "\n"
  out:= out ++ genblock
  --if ifsomeblock.length > 0 ∧ out.length > 0 then
  --  out := out ++ "\n"
  --out:= out ++ ifsomeblock
  if checkIRblock.length > 0 ∧ out.length > 0 then
    out := out ++ "\n"
  out:= out ++ checkIRblock
  if genblock.length + checkIRblock.length > 0 then
    out:= out ++ "\n" ++ returnblock
  else out:= out ++ returnblock
  return out


def checker_where_defs (relation: InductiveInfo) (inpname: List String) (monad: String :="IO") : MetaM String := do
  let mut out_str := ""
  let mut i := 0
  for con in relation.constructors do
    i := i + 1
    let conprops_str := (← con.all_hypotheses.mapM (fun a => Meta.ppExpr a)).map toString
    out_str:= out_str ++ "\n-- Constructor: " ++ toString conprops_str
    out_str:= out_str ++ " → " ++ toString (← Meta.ppExpr con.conclusion) ++ "\n"
    out_str:= out_str ++ (← prototype_for_checker_by_con relation inpname i monad) ++ ":= do \n"
    let bt ← get_checker_backtrack_elem_from_constructor con inpname
    let btStr ← backtrack_elem_toString_checker bt monad
    out_str:= out_str ++ btStr ++ "\n"
  return out_str

syntax (name := getBackTrack) "#get_backtrack_checker" term "with_name" term : command

@[command_elab getBackTrack]
def elabgetBackTrack : CommandElab := fun stx => do
  match stx with
  | `(#get_backtrack_checker $t1:term with_name $t2:term) =>
    Command.liftTermElabM do
      let inpexp ← elabTerm t1 none
      let inpname ← termToStringList t2
      let relation ← getInductiveInfo inpexp
      let where_defs ← checker_where_defs relation inpname
      IO.println where_defs
  | _ => throwError "Invalid syntax"

#get_backtrack_checker typing with_name ["L", "e", "t"]
#get_backtrack_checker balanced with_name ["h", "T"]
#get_backtrack_checker bst with_name ["lo", "hi", "T"]



-- BACKTRACK PRODUCER ---


def get_producer_backtrack_elem_from_constructor (ctor: InductiveConstructor) (inputNames : List String) (genpos: Nat)
      : MetaM BacktrackElem := do
  let temp := Name.mkStr1 "temp000"
  let tempfvar := Expr.fvar (FVarId.mk temp)
  let conclusion_args :=  ctor.conclusion.getAppArgs.set! genpos tempfvar
  let new_conclusion := mkAppN ctor.conclusion.getAppFn conclusion_args
  let conclusion ← separate_fvar new_conclusion
  let args := (conclusion.cond.getAppArgs).toList
  let inputNamesAndArgs := inputNames.zip args
  -- Take all elements of `inputNamesAndArgs`, but omit the element at the `genpos`-th index
  let inputNamesAndArgs := List.eraseIdx inputNamesAndArgs genpos
  -- Find all pairs where the argument is not a free variable
  -- (these are the arguments that need matching)
  let inputPairsThatNeedMatching := inputNamesAndArgs.filter (fun (_, arg) => !arg.isFVar)
  let (inputsToBeMatched, exprsToBeMatched) := inputPairsThatNeedMatching.unzip
  --Get GenCheckCall
  let gccs ← GenCheckCalls_for_producer ctor genpos
  let gcc_group ← GenCheckCalls_grouping gccs
  return {
    inputs := (List.eraseIdx inputNames genpos).toArray
    inputsToBeMatched := inputsToBeMatched.toArray
    exprsToBeMatched := exprsToBeMatched.toArray
    gcc_group := gcc_group
    variableEqualities := conclusion.eqs ++ gcc_group.variableEqualities
  }


def cbe_if_return_producer (cbe: BacktrackElem) (iden: String) (vars: List String) (monad: String :="IO"): MetaM String := do
  let mut out:= ""
  if cbe.variableEqualities.size + cbe.gcc_group.check_nonIR_list.size + cbe.gcc_group.check_IR_list.size > 0 then
    out := out ++ iden ++ "if "
  for j in vars do
    out := out ++ "check" ++ j ++ " && "
  for i in cbe.variableEqualities do
    out := out ++  "(" ++ toString (i.1.name) ++ " == " ++ toString (i.2.name) ++ ") && "
  for gcc in cbe.gcc_group.check_nonIR_list do
    out := out ++ (← GenCheckCalls_toCode gcc monad) ++ " && "
  if cbe.variableEqualities.size + cbe.gcc_group.check_nonIR_list.size + cbe.gcc_group.check_IR_list.size > 0 then
    out:= ⟨out.data.dropLast.dropLast.dropLast⟩ ++ "\n" ++ iden ++  "then "
  for gcc in cbe.gcc_group.ret do
    out := out ++ iden ++ (← GenCheckCalls_toCode gcc monad)
  if cbe.variableEqualities.size + cbe.gcc_group.check_nonIR_list.size + cbe.gcc_group.check_IR_list.size + cbe.gcc_group.ifsome_list.size > 0 then
    let monad_fail := if monad = "IO" then "throw (IO.userError \"fail at checkstep\")" else "return none"
    out := out ++ "\n" ++ monad_fail
  if cbe.inputsToBeMatched.size > 0 then
    let monad_fail := if monad = "IO" then "throw (IO.userError \"fail\")" else "return none"
    out:= out ++ "\n| " ++ makeUnderscores_commas cbe.inputsToBeMatched.size ++ " => " ++ monad_fail
  return out


def backtrack_elem_toString_producer (cbe: BacktrackElem) (monad: String :="IO"): MetaM String := do
  let mut out := ""
  let matchblock ← cbe_match_block cbe
  let (genblock, iden) ← cbe_gen_block cbe monad
  --let (ifsomeblock, iden) ← cbe_ifsome_block cbe monad
  let (checkIRblock, vars) ← cbe_gen_check_IR_block cbe iden monad
  let returnblock ← cbe_if_return_producer cbe iden vars monad
  out := out ++ matchblock
  if genblock.length + checkIRblock.length + returnblock.length > 0  ∧ out.length > 0 then
    out := out ++ "\n"
  out:= out ++ genblock
  --if ifsomeblock.length > 0 ∧ out.length > 0 then
  --  out := out ++ "\n"
  --out:= out ++ ifsomeblock
  if checkIRblock.length > 0 ∧ out.length > 0 then
    out := out ++ "\n"
  out:= out ++ checkIRblock
  if genblock.length + checkIRblock.length > 0 then
    out:= out ++ "\n" ++ returnblock
  else out:= out ++ returnblock
  return out


def producer_where_defs (relation: InductiveInfo) (inpname: List String) (genpos: Nat) (monad: String :="IO"): MetaM String := do
  let mut out_str := ""
  let mut i := 0
  for ctor in relation.constructors do
    i := i + 1
    let conprops_str := (← ctor.all_hypotheses.mapM (fun a => Meta.ppExpr a)).map toString
    out_str:= out_str ++ "\n-- Constructor: " ++ toString conprops_str
    out_str:= out_str ++ " → " ++ toString (← Meta.ppExpr ctor.conclusion) ++ "\n"
    out_str:= out_str ++ (← prototype_for_producer_by_con relation inpname genpos i monad) ++ ":= do\n"
    let bt ← get_producer_backtrack_elem_from_constructor ctor inpname genpos
    let btStr ← backtrack_elem_toString_producer bt monad
    out_str:= out_str ++ btStr ++ "\n"
  return out_str


syntax (name := getBackTrackProducer) "#get_backtrack_producer" term "with_name" term "for_arg" num: command

@[command_elab getBackTrackProducer]
def elabgetBackTrackProducer : CommandElab := fun stx => do
  match stx with
  | `(#get_backtrack_producer $t1:term with_name $t2:term for_arg $t3) =>
    Command.liftTermElabM do
      let input_expr ← elabTerm t1 none
      let inpname ← termToStringList t2
      let pos := TSyntax.getNat t3
      let inductiveInfo ← getInductiveInfo input_expr
      let where_defs ← producer_where_defs inductiveInfo inpname pos
      IO.println where_defs
  | _ => throwError "Invalid syntax"

#get_backtrack_producer typing with_name ["L", "e", "t"] for_arg 0
#get_backtrack_producer typing with_name ["L", "e", "t"] for_arg 2
#get_backtrack_producer typing with_name ["L", "e", "t"] for_arg 1
#get_backtrack_producer balanced with_name ["h", "T"] for_arg 1
#get_backtrack_producer bst with_name ["lo", "hi", "T"] for_arg 2


end Plausible.IR
