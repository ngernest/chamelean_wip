import Lean
import Std
import Plausible
open List Nat Array String
open Lean Elab Command Meta Term
open Plausible


def uniform_backtrack_codeblock (btarray: Array String) (inps: List String) (backtracknum: Nat) : MetaM String := do
  let mut body := " for _i in [1:" ++ toString backtracknum ++ "] do\n"
  body:= body ++ "  let f ← uniform_backtracking_IO #["
  for bt in btarray do
    body := body ++ bt ++ ", "
  body:= ⟨body.data.dropLast.dropLast⟩ ++ "]\n  let ret ← MetaM_to_option (f size "
  for i in inps do
    body:= body ++ i ++ " "
  body:= ⟨body.data.dropLast⟩ ++ ")\n"
  body:= body ++ "  match ret with\n"
  body:= body ++ "  | some ret => return ret\n"
  body:= body ++ "  | _ => continue\n"
  body:= body ++ " throwError \"fail\""
  return body

def weight_backtrack_codeblock (btarray: Array String) (inps: List String) (backtracknum: Nat) (low_weight_size: Nat): MetaM String := do
  let mut body := " for _i in [1:" ++ toString backtracknum ++ "] do\n"
  body:= body ++ "  let f ← weight_backtracking_IO #["
  for bt in btarray do
    body := body ++ bt ++ ", "
  body:= ⟨body.data.dropLast.dropLast⟩ ++ "] " ++ toString low_weight_size ++ " size"
  body:= body ++ "\n  let ret ← MetaM_to_option (f size "
  for i in inps do
    body:= body ++ i ++ " "
  body:= ⟨body.data.dropLast⟩ ++ ")\n"
  body:= body ++ "  match ret with\n"
  body:= body ++ "  | some ret => return ret\n"
  body:= body ++ "  | _ => continue\n"
  body:= body ++ " throwError \"fail\""
  return body

partial def get_types_chain (type : Expr) : MetaM (Array Expr) := do
  let rec helper (e : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
    match e with
    | Expr.forallE _ domain body _ =>
      helper (body.instantiate1 (mkFVar ⟨`x⟩)) (acc.push domain)
    | e => return acc.push e
  let types ← helper type #[]
  return types

inductive Tree  where
| Leaf : Nat → Tree
| Node : Nat → Tree  → Tree  → Tree


structure IT_constructor where
  ITname : Name
  conname: Name
  args: List Expr

structure IT_info where
  name : Name
  noinstance : Array Expr
  constructors : Array IT_constructor

#check SampleableExt

def is_ind_IT_constructor (ITname: Name )(conargs: List Expr) : Bool := match conargs with
| [] => false
| h::t => (h.constName == ITname) || is_ind_IT_constructor ITname t


def has_instance (e: Expr) : MetaM Bool := do
  let exprTyp ← inferType e
  let .sort u ← whnf (← inferType exprTyp) | throwError m!"{exprTyp} is not a type"
  let .succ u := u | throwError m!"{exprTyp} is not a type with computational content"
  let v ← mkFreshLevelMVar
  let app ← synthInstance? (mkApp (mkConst ``SampleableExt [u, v]) e)
  let v ← instantiateLevelMVars v
  match app with
  | some _ => return true
  | _ => return false

def extract_IT_info (inpexp : Expr) : MetaM (IT_info) := do
  match inpexp.getAppFn.constName? with
  | some typeName => do
    let env ← getEnv
    match env.find? typeName with
    | none => throwError "Type '{typeName}' not found"
    | some (ConstantInfo.inductInfo info) => do
      let mut constructors : Array IT_constructor := #[]
      let mut noinstance : Array Expr := #[]
      for ctorName in info.ctors do
        let some ctor := env.find? ctorName
         | throwError "IRConstructor '{ctorName}' not found"
        let ctys ←  get_types_chain ctor.type
        let cargs := ctys.toList.dropLast
        for a in cargs do
          if ¬ (← has_instance a) then noinstance:= noinstance.push a
        constructors := constructors.push ⟨typeName, ctor.name, cargs⟩
      IO.println s!"No inst {noinstance}"
      --let nonind_constructors:= constructors.filter (fun x => is_ind_IT_constructor typeName x.args)
      --let ind_constructors:= constructors.filter (fun x =>  (is_ind_IT_constructor typeName x.args == false))
      return ⟨typeName, noinstance, constructors⟩
    | some _ =>
      throwError "'{typeName}' is not an inductive type"
  | none => throwError "Not a type"


def generatorCode_for_IT_constructor (con: IT_constructor) (order: Nat) : MetaM String :=do
  let mut out:= ""
  let mut i:= 0
  let conname:= con.conname.toString
  let ITname:= con.ITname.toString
  for v in con.args do
    if v.constName = con.ITname then
      out:= out ++ "let var" ++ toString i ++ " ← gen_" ++ ITname ++  " size \n"
    else
      out:= out ++ "let var" ++ toString i ++ " ← SampleableExt.interpSample " ++ v.constName.toString ++ "\n"
    i := i + 1
  let mut ret := "return " ++ conname
  for j in [0:con.args.length] do
    ret := ret ++ " var" ++ toString j ++ " "
  ret := ret ++ "\n"
  out:= out ++ ret
  let prototype := "def gen_"++ ITname ++ "_by_con_" ++ toString order ++  " (size : Nat) : Gen "++ ITname ++ " := do\n"
  out := prototype ++ out
  return out

def ind_backtrack_list_for_IT (r: IT_info): MetaM (Array String) := do
  let mut i := 0
  let name := r.name.toString
  let mut out : Array String := #[]
  for con in r.constructors do
    i := i + 1
    if is_ind_IT_constructor r.name con.args then
      let bt := "gen_" ++ name ++"_by_con_" ++ toString i
      out:= out.push bt
  return out

def nonind_backtrack_list_for_IT (r: IT_info): MetaM (Array String) := do
  let mut i := 0
  let name := r.name.toString
  let mut out : Array String := #[]
  for con in r.constructors do
    i := i + 1
    if ¬ is_ind_IT_constructor r.name con.args then
      let bt := "gen_" ++ name ++"_by_con_" ++ toString i
      out:= out.push bt
  return out


def IT_gen (r: IT_info)  (backtracknum: Nat): MetaM (String) := do
  let prototype := "def gen_"++ toString r.name  ++  " (size : Nat) : Gen "++ toString r.name ++ " := do\n"
  let mut body := "match size with \n| zero => \n"
  let bt0 ← nonind_backtrack_list_for_IT r
  let btblock ← uniform_backtrack_codeblock bt0 [] backtracknum
  body := body ++ btblock
  body:= body ++ "\n| succ size => \n"
  let btpos ← ind_backtrack_list_for_IT r
  let bts:= bt0.append btpos
  let btblock ← weight_backtrack_codeblock bts [] backtracknum bt0.size
  body := body ++ btblock
  return prototype ++ body

def get_mutual_rec_block_for_IT (r: IT_info)  (btnum: Nat) : MetaM String := do
  let generator ←  IT_gen r btnum
  let mut mc_block := "mutual\n-- By_Cons \n" ++ generator ++ " \n"
  let mut order := 0
  for con in r.constructors do
    IO.println s!"Con {con.args}"
    order := order + 1
    let cons_gen ← generatorCode_for_IT_constructor con order
    mc_block := mc_block ++ cons_gen
  mc_block := mc_block ++ "\nend"
  return mc_block

def print_m_string (m: MetaM String) : MetaM Unit :=do
  IO.println s!"{← m}"

syntax (name := genmutualrec) "#gen_mutual_rec_IT" term  "backtrack" num: command

@[command_elab genmutualrec]
def elabGetMutualBlock : CommandElab := fun stx => do
  match stx with
  | `(#gen_mutual_rec_IT $t backtrack $t3) =>
    Command.liftTermElabM do
      let e ← elabTerm t none
      let it ←  extract_IT_info e
      let btnum := TSyntax.getNat t3
      let mc_block := get_mutual_rec_block_for_IT it btnum
      print_m_string mc_block
  | _ => throwError "Invalid syntax"

#gen_mutual_rec_IT Tree backtrack 1
