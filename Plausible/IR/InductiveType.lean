import Lean
import Std
import Plausible
import Plausible.IR.Example
import Plausible.IR.Extractor
import Plausible.IR.Prelude
import Plausible.IR.Prototype
import Plausible.IR.GCCall
import Plausible.IR.Constructor
import Plausible.IR.Backtrack
open List Nat Array String
open Lean Elab Command Meta Term
open Lean.Parser.Term
open Plausible Gen


namespace Plausible.IR


structure IT_constructor where
  ITname : Name
  conname: Name
  args: List Expr
  is_inductive : Bool

structure IT_info where
  name : Name
  has_instance: Bool
  noinstance_dep : Array Expr
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
          if (¬ (← has_instance a)) ∧ (¬ a.constName = typeName) ∧  (¬ a.constName ∈ noinstance.map Expr.constName)
          then noinstance:= noinstance.push a
        let is_ind := is_ind_IT_constructor typeName cargs
        constructors := constructors.push ⟨typeName, ctor.name, cargs, is_ind⟩
      --IO.println s!"No inst {noinstance}"
      --let nonind_constructors:= constructors.filter (fun x => is_ind_IT_constructor typeName x.args)
      --let ind_constructors:= constructors.filter (fun x =>  (is_ind_IT_constructor typeName x.args == false))
      return ⟨typeName, ← has_instance inpexp, noinstance, constructors⟩
    | some _ =>
      throwError "'{typeName}' is not an inductive type"
  | none => throwError "Not a type"


def generatorCode_for_IT_constructor (con: IT_constructor): MetaM String :=do
  let mut out:= ""
  let mut i:= 0
  let conname:= con.conname.toString
  let ITname:= con.ITname.toString
  for v in con.args do
    if v.constName = con.ITname then
      out:= out ++ "  let var" ++ toString i ++ " ← gen_" ++ ITname ++  " (size -1) \n"
    else
      out:= out ++ "  let var" ++ toString i ++ " ← SampleableExt.interpSample " ++ v.constName.toString ++ "\n"
    i := i + 1
  let mut ret := "  return " ++ conname
  for j in [0:con.args.length] do
    ret := ret ++ " var" ++ toString j ++ " "
  ret := ret ++ "\n"
  out:= out ++ ret
  --let prototype := "let gen_"++ ITname ++ "_by_con_" ++ toString order ++  " : Gen "++ ITname ++ " := do\n"
  --out := prototype ++ out
  return out

def ind_backtrack_list_for_IT (r: IT_info): MetaM (Array String) := do
  let mut i := 0
  let name := r.inductive_name.toString
  let mut out : Array String := #[]
  for con in r.constructors do
    i := i + 1
    if is_ind_IT_constructor r.name con.args then
      let bt := "gen_" ++ name ++"_by_con_" ++ toString i
      out:= out.push bt
  return out

def nonind_backtrack_list_for_IT (r: IT_info): MetaM (Array String) := do
  let mut i := 0
  let name := r.inductive_name.toString
  let mut out : Array String := #[]
  for con in r.constructors do
    i := i + 1
    if ¬ is_ind_IT_constructor r.name con.args then
      let bt := "gen_" ++ name ++"_by_con_" ++ toString i
      out:= out.push bt
  return out




def uniform_backtrack_codeblock_IT (btarray: Array String) : MetaM String := do
  let mut body := "  ← uniform_backtracking_Gen #["
  for bt in btarray do
    body := body ++ bt ++ ", "
  body:= ⟨body.data.dropLast.dropLast⟩ ++ "] (by simp)"
  return body

def weight_backtrack_codeblock_IT (btarray: Array String) (low_weight_size: Nat): MetaM String := do
  let mut body :=  " ← weight_backtracking_Gen #["
  for bt in btarray do
    body := body ++ bt ++ ", "
  body:= ⟨body.data.dropLast.dropLast⟩ ++ "] " ++ toString low_weight_size ++ " size (by simp) (by omega)"
  return body



def IT_gen (r: IT_info) : MetaM (String) := do
  let prototype := "def gen_"++ toString r.name  ++  " (size : Nat) : Gen "++ toString r.name ++ " := do\n"
  let bt0 ← nonind_backtrack_list_for_IT r
  let mut order := 1
  let ITname:= r.inductive_name.toString
  let mut body:= ""
  for con in r.constructors do
    let con_prototype := "let gen_"++ ITname ++ "_by_con_" ++ toString order ++  " : Gen "++ ITname ++ " := do\n"
    let con_code ← generatorCode_for_IT_constructor con
    body:=body ++ con_prototype
    if con.is_inductive then
      body:= body ++ "  if size = 0 then ← uniform_backtracking_Gen #["
      for bt in bt0 do
        body := body ++ bt ++ ", "
      body:= ⟨body.data.dropLast.dropLast⟩ ++ "] (by simp)\n  else\n"
    body:= body ++ con_code
    order:= order + 1
  body := body ++ "match size with \n| zero => \n"
  let btblock ← uniform_backtrack_codeblock_IT bt0
  body := body ++ btblock
  body:= body ++ "\n| succ size => \n"
  let btpos ← ind_backtrack_list_for_IT r
  let bts:= bt0.append btpos
  let btblock ← weight_backtrack_codeblock_IT bts bt0.size
  body := body ++ btblock
  return prototype ++ body


def instance_def_code (r: IT_info) (size: Nat): MetaM (String × String × String) :=do
  let gencode ← IT_gen r
  let instance_def := "instance : SampleableExt " ++ r.inductive_name.toString
      ++ ":= SampleableExt.mkSelfContained (gen_" ++ r.inductive_name.toString ++ " " ++ toString size ++")"
  let shrinkable := "instance : Shrinkable " ++ r.inductive_name.toString ++ " where shrink := fun x => [x]"
  return (shrinkable, gencode, instance_def)

syntax (name := genIT) "#gen_IT" term : command

@[command_elab genIT]
def elabGetMutualBlock : CommandElab := fun stx => do
  match stx with
  | `(#gen_IT $t:term) =>
    Command.liftTermElabM do
      let e ← elabTerm t none
      let it ←  extract_IT_info e
      let mc_block := IT_gen it
      print_m_string mc_block
  | _ => throwError "Invalid syntax"

#gen_IT Tree


syntax (name := derivesamplable) "#derive_sampleable" term "with_size" num : command

@[command_elab derivesamplable]
def elabDeriveGenerator : CommandElab := fun stx => do
  match stx with
  | `(#derive_sampleable $t with_size $t2) =>
      let (shrinkable, code, instance_def) ← Command.liftTermElabM do
        let e ←  elabTerm t none
        let size := TSyntax.getNat t2
        let it ←  extract_IT_info e
        instance_def_code it size
      parseCommand shrinkable
      parseCommand code
      parseCommand instance_def
  | _ => throwError "Invalid syntax"




#derive_sampleable Tree with_size 5

--instance : SampleableExt Tree :=
--  SampleableExt.mkSelfContained (gen_Tree 3)



#eval Gen.run (SampleableExt.interpSample Tree) 5

end Plausible.IR
