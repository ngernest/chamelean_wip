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

-- Process condition ---

def contains_in_list (f:FVarId) (a: List FVarId):= match a with
| [] => false
| h::t => h == f || contains_in_list f t

def contains_in (f:FVarId) (a: Array FVarId):= contains_in_list f a.toList

def in_a_not_in_b_list (a b: List FVarId) := match a with
| [] => []
| h::t => if contains_in_list h b then in_a_not_in_b_list t b else h::in_a_not_in_b_list t b

def in_a_not_in_b (a b: Array FVarId) := (in_a_not_in_b_list a.toList b.toList).toArray

def in_a_and_b_list (a b: List FVarId) := match a with
| [] => []
| h::t => if contains_in_list h b then h::in_a_and_b_list t b else in_a_and_b_list t b

def in_a_and_b (a b: Array FVarId) := (in_a_and_b_list a.toList b.toList).toArray

def list_append_non_repeat (a b : List FVarId) := match b with
| [] => a
| h::t => if contains_in_list h a == false then list_append_non_repeat (a ++ [h]) t
          else  list_append_non_repeat a t

def append_non_repeat (a b : Array FVarId) := (list_append_non_repeat a.toList b.toList).toArray

def count_fvars_in (e: Expr) (id: FVarId) : Nat :=
  match e with
  | Expr.fvar fid => if id == fid then 1 else 0
  | Expr.app f a =>
    let c1 := count_fvars_in f id
    let c2 := count_fvars_in a id
    c1 + c2
  | _ => 0

def all_FVars_in (e: Expr) : Array FVarId :=
  match e with
  | Expr.fvar fid => #[fid]
  | Expr.app f a => append_non_repeat (all_FVars_in f) (all_FVars_in a)
  | _ => #[]

def subst_first_fVar (e: Expr) (old : FVarId) (new : FVarId) : MetaM Expr := do
  if ¬ e.containsFVar old then return e
  else
    match e with
    | Expr.fvar id =>
      if id == old then return (Expr.fvar new) else return e
    | Expr.app f a =>
      if f.containsFVar old then
        let fnew ← subst_first_fVar f old new
        return Expr.app fnew a
      else
        let anew ← subst_first_fVar a old new
        return Expr.app f anew
    | _ => return e

structure split_inductive_cond where
  cond : Expr
  fvarids : Array FVarId
  eqs: Array (FVarId × FVarId)

/- for any Fvar t appear more than 1 time in the expr, keep the first one as t
    replace the second one with t1, the third one with t2 ....
    record the equations t = t1, t = t2 .... -/
def separate_fvar (cond: Expr): MetaM split_inductive_cond := do
  let fvars := all_FVars_in cond
  let mut eq_arr: Array (FVarId × FVarId) := #[]
  let mut fvarids := fvars
  let temp := Name.mkStr1 "temp000"
  let tempfvarid := FVarId.mk temp
  let mut new_out := cond
  for fv in fvars do
    let mut i := 0
    let mut currentfv := fv
    while (count_fvars_in new_out currentfv > 1) do
      let newname := Name.mkStr1 (fv.name.toString  ++ toString i)
      let newfvarid := FVarId.mk newname
      new_out ← subst_first_fVar new_out currentfv tempfvarid
      new_out := new_out.replaceFVarId currentfv (mkFVar newfvarid)
      new_out := new_out.replaceFVarId tempfvarid (mkFVar currentfv)
      i:= i + 1
      currentfv := newfvarid
      eq_arr:= eq_arr.push (fv, newfvarid)
      fvarids := fvarids.push newfvarid
  return {
    cond:= new_out
    fvarids:= fvarids
    eqs:= eq_arr
  }

def separate_fvar_in_cond (cond: Expr) (initset: Array FVarId) (cond_pos: Nat): MetaM split_inductive_cond := do
  let fvars := all_FVars_in cond
  let fvars_init := in_a_and_b fvars initset
  let mut newcond := cond
  let mut eqs : Array (FVarId × FVarId) := #[]
  for f in fvars_init do
    let newname := Name.mkStr1 (f.name.toString ++ "_" ++ toString cond_pos)
    let newfvarid := FVarId.mk newname
    newcond := newcond.replaceFVarId f (mkFVar newfvarid)
    eqs := eqs.push (f,newfvarid)
  let sep ← separate_fvar newcond
  let newsep := {
    cond:= sep.cond
    fvarids:= fvars_init ++ sep.fvarids
    eqs := eqs ++ sep.eqs
  }
  return newsep



--TO BE IMPLEMENT-- separate function call with constructor
def is_inductive_constructor (e: Expr) : Bool := ¬ e.isFVar


inductive GenCheckCall where
  | check_IR (cond: Expr) : GenCheckCall
  | check_nonIR (cond: Expr) : GenCheckCall
  | gen_IR (id: FVarId) (cond: Expr) (pos: Nat): GenCheckCall
  | mat (id: FVarId) (sp : split_inductive_cond) : GenCheckCall
  | gen_fvar (id: FVarId) (type: Expr) : GenCheckCall
  | ret (e: Expr): GenCheckCall

def get_checker_initset (c: IRConstructor) : Array FVarId := all_FVars_in c.out_prop

def get_producer_initset (c: IRConstructor) (genpos: Nat): MetaM (Array FVarId) := do
  if genpos ≥ c.out_args.size then throwError "invalid gen position"
  let mut i := 0
  let mut outarr : Array FVarId := #[]
  for e in c.out_args do
    if ¬ i = genpos then outarr := append_non_repeat outarr (all_FVars_in e)
    i:= i + 1
  return outarr

def get_producer_outset (c: IRConstructor) (genpos: Nat): MetaM (Array FVarId) := do
  if h: genpos ≥ c.out_args.size then throwError "invalid gen position"
  else
    let initset ← get_producer_initset c genpos
    let gen_arg := c.out_args[genpos]
    --let gen_arg := c.out_args.get genpos (by omega)
    let outvar := all_FVars_in gen_arg
    let mut outarr : Array FVarId := #[]
    for i in initset do
      if ¬ contains_in i outvar then outarr:=outarr.push i
    return outarr

def get_uninit_set (cond: Expr) (initset : Array FVarId) := in_a_not_in_b (all_FVars_in cond) initset

def fully_init (cond: Expr) (initset : Array FVarId) := (get_uninit_set cond initset).size == 0

def get_last_uninit (cond: Expr) (initset : Array FVarId): MetaM (Option Nat) := do
  if  ¬ (← is_pure_inductive_cond cond) then throwError "not a inductive cond to get_last_uninit_arg "
  let args:= cond.getAppArgs
  let mut i:=0
  let mut pos:=args.size + 1
  for arg in args do
    if ¬ fully_init arg initset then pos :=i
    i:= i + 1
  if pos = args.size + 1 then return none else return some pos

def get_last_uninit_arg_and_uninitset (cond: Expr) (initset : Array FVarId): MetaM (Nat × Array FVarId × Array FVarId) := do
  if  ¬ (← is_pure_inductive_cond cond) then throwError "not a inductive cond to get_last_uninit_arg "
  let args:= cond.getAppArgs
  let mut i:=0
  let mut pos:=args.size + 1
  let mut uninit_arg:= args[0]!
  let mut tobeinit : Array FVarId := #[]
  for arg in args do
    if ¬ fully_init arg initset then
      {
        pos :=i;
        uninit_arg := arg;
        tobeinit := all_FVars_in arg
      }
    i:= i + 1
  if pos = args.size + 1 then return (args.size + 1, #[], #[])
  let mut uninitset : Array FVarId := #[]
  i := 0
  for e in args do
    if ¬ i = pos then uninitset := append_non_repeat uninitset (get_uninit_set e initset)
  uninitset := in_a_not_in_b uninitset tobeinit
  return (pos, uninitset, tobeinit)


def GenCheckCalls_for_cond_props  (c: IRConstructor) (initset0: Array FVarId) : MetaM (Array GenCheckCall) := do
  let mut outarr : Array GenCheckCall := #[]
  let mut initset := initset0
  let mut i := 0
  for cond in c.cond_props do
    /-let namearr := initset.map FVarId.name
    IO.println s!" initset : {namearr}"
    let namearr := (all_FVars_in cond).map FVarId.name
    IO.println s!" All fvars : {namearr}"
    let namearr := (get_uninit_set cond initset).map FVarId.name
    IO.println s!" All uninit fvars : {namearr}"-/
    i := i + 1
    if ← is_inductive_cond cond c then
      --IO.println s!" cond : {cond}"
      if fully_init cond initset then
        outarr := outarr.push (GenCheckCall.check_IR cond)
      else
        let (pos, uninitset, tobeinit) ← get_last_uninit_arg_and_uninitset cond initset
        for fid in uninitset do
          let ty :=  c.varid_type.get! fid
          outarr := outarr.push (GenCheckCall.gen_fvar fid ty)
        let gen_arg := cond.getAppArgs[pos]!
        initset := append_non_repeat initset uninitset
        if gen_arg.isFVar then
          let genid := gen_arg.fvarId!
          outarr := outarr.push (GenCheckCall.gen_IR genid cond pos)
        else
          let genname := Name.mkStr1 ("tcond" ++ toString i)
          let genid := FVarId.mk genname
          let sp ←  separate_fvar_in_cond gen_arg initset i
          outarr := outarr.push (GenCheckCall.gen_IR genid cond pos)
          outarr := outarr.push (GenCheckCall.mat genid sp)
        initset := append_non_repeat initset tobeinit
    else
      if fully_init cond initset then
        outarr := outarr.push (GenCheckCall.check_nonIR cond)
      else
        let uninitset := get_uninit_set cond initset
        /-let namearr := uninitset.map FVarId.name
        IO.println s!" All uninit fvars : {namearr}"-/
        for fid in uninitset do
          let ty :=  c.varid_type.get! fid
          outarr := outarr.push (GenCheckCall.gen_fvar fid ty)
        initset := append_non_repeat initset uninitset
        outarr := outarr.push (GenCheckCall.check_nonIR cond)
  return outarr

def GenCheckCalls_for_checker (c: IRConstructor) : MetaM (Array GenCheckCall) := do
  let mut initset := get_checker_initset c
  let mut outarr ← GenCheckCalls_for_cond_props c initset
  --outarr := outarr.push (GenCheckCall.check_IR c.out_prop)
  return outarr

def GenCheckCalls_for_producer (c: IRConstructor) (genpos: Nat) : MetaM (Array GenCheckCall) := do
  let mut initset ←  get_producer_initset c genpos
  let mut outarr ← GenCheckCalls_for_cond_props c initset
  for cond in c.cond_props do
    initset := append_non_repeat initset (all_FVars_in cond)
  let gen_arg := c.out_prop.getAppArgs[genpos]!
  let uninitset := in_a_not_in_b (all_FVars_in gen_arg) initset
  for fid in uninitset do
    let ty :=  c.varid_type.get! fid
    outarr := outarr.push (GenCheckCall.gen_fvar fid ty)
  outarr := outarr.push (GenCheckCall.ret gen_arg)
  return outarr

def GenCheckCalls_toStr (c: GenCheckCall) : MetaM String := do
  match c with
  | GenCheckCall.check_IR cond => return  "check_IR_" ++ toString (← Meta.ppExpr cond)
  | GenCheckCall.check_nonIR cond => return  "check_nonIR_" ++ toString (← Meta.ppExpr cond)
  | GenCheckCall.gen_IR _ cond pos =>  return  "gen_IR_" ++ toString (← Meta.ppExpr cond) ++ " at "  ++ toString pos
  | GenCheckCall.mat id sp => return "match " ++ id.name.toString ++ toString (← Meta.ppExpr sp.cond)
  | GenCheckCall.gen_fvar id ty=>  return  "gen_fvar " ++ toString (id.name) ++ ": " ++ toString (← Meta.ppExpr ty)
  | GenCheckCall.ret e =>  return  "ret " ++ toString (← Meta.ppExpr e)

def gen_IR_at_pos (id: FVarId) (cond: Expr) (pos: Nat) : MetaM String := do
  let tt := Lean.mkFVar ⟨Name.mkStr1 "tt"⟩
  let new_args := cond.getAppArgs.set! pos tt
  let new_cond := Lean.mkAppN cond.getAppFn new_args
  let fun_proto := "fun tt => " ++ toString (← Meta.ppExpr new_cond)
  return "let " ++ toString (id.name)  ++ ":= gen_IR (" ++ fun_proto ++ ")"


def GenCheckCalls_toRawCode (c: GenCheckCall) : MetaM String := do
  match c with
  | GenCheckCall.check_IR cond => return  "check_IR (" ++ toString (← Meta.ppExpr cond) ++ ")"
  | GenCheckCall.check_nonIR cond => return  "check (" ++ toString (← Meta.ppExpr cond) ++ ")"
  | GenCheckCall.gen_IR id cond pos => gen_IR_at_pos id cond pos
  | GenCheckCall.mat id sp => return  "if let " ++ toString (← Meta.ppExpr sp.cond) ++ ":= " ++ toString (id.name) ++ " then "
  | GenCheckCall.gen_fvar id ty =>  return  "let " ++ toString (id.name) ++ ":= gen_rand " ++ toString (← Meta.ppExpr ty)
  | GenCheckCall.ret e => return "return " ++ toString (← Meta.ppExpr e)



syntax (name := getChekerCall) "#get_checker_call" term : command

@[command_elab getChekerCall]
def elabCheckerCall : CommandElab := fun stx => do
  match stx with
  | `(#get_checker_call $t1:term) =>
    Command.liftTermElabM do
      let inpexp ← elabTerm t1 none
      let relation ← extract_IR_info inpexp
      for con in relation.constructors do
        IO.println s!"\n---- Cond prop : {con.cond_props}"
        IO.println s!"---- Out prop : {con.out_prop}"
        let proc_conds ← GenCheckCalls_for_checker con
        for pc in proc_conds do
          IO.println (← GenCheckCalls_toRawCode pc)
  | _ => throwError "Invalid syntax"


#get_checker_call typing
#get_checker_call balanced
#get_checker_call bst

syntax (name := geGenCall) "#get_producer_call" term "for_arg" num : command

@[command_elab geGenCall]
def elabGenCall : CommandElab := fun stx => do
  match stx with
  | `(#get_producer_call $t1:term for_arg $t2) =>
    Command.liftTermElabM do
      let inpexp ← elabTerm t1 none
      let pos := TSyntax.getNat t2
      let relation ← extract_IR_info inpexp
      for con in relation.constructors do
        IO.println s!"\n---- Cond prop : {con.cond_props}"
        IO.println s!"---- Out prop : {con.out_prop}"
        let proc_conds ← GenCheckCalls_for_producer con pos
        for pc in proc_conds do
          IO.println (← GenCheckCalls_toRawCode pc)
  | _ => throwError "Invalid syntax"


#get_producer_call typing for_arg 2
#get_producer_call balanced for_arg 1
#get_producer_call bst for_arg 2

end Plausible.IR
