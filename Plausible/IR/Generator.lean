import Lean
import Std
import Plausible.IR.Example
import Plausible.IR.Extractor
import Plausible.IR.Prelude
import Plausible.IR.Prototype
import Plausible.IR.GCCall
import Plausible.IR.Constructor
import Plausible.IR.Backtrack
import Lean.Elab.Deriving.DecEq
import Lean.Meta.Tactic.Simp.Main
open Lean.Elab.Deriving.DecEq
open List Nat Array String
open Lean Elab Command Meta Term
open Lean.Parser.Term


namespace Plausible.IR
-- Generate function --


def get_checker (r: IR_info) (inpname: List String) (btnum: Nat) : MetaM String := do
  let prototype ←  prototype_for_checker r inpname
  let body ← checker_body r inpname btnum
  let where_def ← checker_where_defs r inpname
  let checker := where_def ++ "\n" ++ prototype ++ " := do\n" ++ body ++ "\n"
  return checker


syntax (name := genchecker) "#gen_checker" term "with_name" term "backtrack" num: command

@[command_elab genchecker]
def elabGetChecker : CommandElab := fun stx => do
  match stx with
  | `(#gen_checker $t with_name $t2:term backtrack $t3) =>
    Command.liftTermElabM do
      let e ← elabTerm t none
      let inpname ← termToStringList t2
      let relation ←  extract_IR_info_with_inpname e inpname
      let btnum := TSyntax.getNat t3
      let checker := get_checker relation inpname btnum
      print_m_string checker
  | _ => throwError "Invalid syntax"

#gen_checker typing with_name ["L", "e", "t"] backtrack 100
#gen_checker balanced with_name ["h", "T"] backtrack 100
#gen_checker bst with_name ["lo", "hi", "T"] backtrack 100

def get_producer (r: IR_info) (inpname: List String) (genpos: Nat) (btnum: Nat): MetaM String := do
  let prototype ←  prototype_for_producer r inpname genpos
  let body ← producer_body r inpname genpos btnum
  let where_def ← producer_where_defs r inpname genpos
  let producer := where_def ++ "\n" ++ prototype ++ " := do\n" ++ body ++ "\n"
  return producer


syntax (name := genproducer) "#gen_producer" term "with_name" term "for_arg" num "backtrack" num: command

@[command_elab genproducer]
def elabGetProducer : CommandElab := fun stx => do
  match stx with
  | `(#gen_producer $t with_name $t2:term for_arg $t3 backtrack $t4) =>
    Command.liftTermElabM do
      let e ← elabTerm t none
      let inpname ← termToStringList t2
      let relation ←  extract_IR_info_with_inpname e inpname
      let pos := TSyntax.getNat t3
      let btnum := TSyntax.getNat t4
      let producer := get_producer relation inpname pos btnum
      print_m_string producer
  | _ => throwError "Invalid syntax"

#gen_producer typing with_name ["L", "e", "t"] for_arg 2 backtrack 100
#gen_producer balanced with_name ["h", "T"] for_arg 1 backtrack 100
#gen_producer bst with_name ["lo", "hi", "T"] for_arg 2 backtrack 100


def get_mutual_rec_block (r: IR_info) (inpname: List String) (btnum: Nat) : MetaM String := do
  let checker ←  get_checker r inpname btnum
  let mut mc_block := "mutual\n-- CHECKER \n " ++ checker
  for pos in [0:r.inp_types.size] do
    let producer ← get_producer r inpname pos btnum
    mc_block := mc_block ++ "\n-- GENERATOR FOR ARG" ++ toString pos ++ "\n" ++ producer
  mc_block := mc_block ++ "\nend"
  return mc_block

syntax (name := genmutualrec) "#gen_mutual_rec" term "with_name" term "backtrack" num: command

@[command_elab genmutualrec]
def elabGetMutualBlock : CommandElab := fun stx => do
  match stx with
  | `(#gen_mutual_rec $t with_name $t2:term backtrack $t3) =>
    Command.liftTermElabM do
      let e ← elabTerm t none
      let inpname ← termToStringList t2
      let relation ←  extract_IR_info_with_inpname e inpname
      let btnum := TSyntax.getNat t3
      let mc_block := get_mutual_rec_block relation inpname btnum
      print_m_string mc_block
  | _ => throwError "Invalid syntax"

#gen_mutual_rec typing with_name ["L", "e", "t"] backtrack 100
#gen_mutual_rec balanced with_name ["h", "T"] backtrack 100
#gen_mutual_rec bst with_name ["lo", "hi", "T"] backtrack 100

def get_testfile (r: IR_info) (inpname: List String) (btnum: Nat) : MetaM String := do
  let mut importblock := "import Lean \nimport Plausible.IR_example\nimport Plausible.IR_backtrack\n"
  importblock := importblock ++ "open List Nat Array String\n"
  importblock := importblock ++ "open Lean Elab Command Meta Term\n"
  let mut mc_block ← get_mutual_rec_block r inpname btnum
  return importblock ++ "\n" ++ mc_block

syntax (name := writemutualrec) "#writefile_mutual_rec" term "with_name" term "backtrack" num "tofile" str: command

@[command_elab writemutualrec]
def elabWriteMutualBlock : CommandElab := fun stx => do
  match stx with
  | `(#writefile_mutual_rec $t with_name $t2:term backtrack $t3 tofile $t4) =>
    Command.liftTermElabM do
      let e ← elabTerm t none
      let inpname ← termToStringList t2
      let filename := TSyntax.getString t4
      let relation ←  extract_IR_info_with_inpname e inpname
      let btnum := TSyntax.getNat t3
      let mc_block ←  get_testfile relation inpname btnum
      let path := System.FilePath.mk "Plausible" / "TestIR" / filename
      IO.FS.writeFile path.toString mc_block
  | _ => throwError "Invalid syntax"

--#writefile_mutual_rec typing with_name ["L", "e", "t"] backtrack 100 tofile "typing.lean"
--#writefile_mutual_rec balanced with_name ["h", "T"] backtrack 100 tofile "balanced.lean"
--#writefile_mutual_rec bst with_name ["lo", "hi", "T"] backtrack 100 tofile "bst.lean"

def parseFunction (input : String) : CommandElabM Unit := do
  let env ← getEnv
  match Parser.runParserCategory env `command input with
  | Except.ok stx =>
    IO.println s!"Parsed successfully: {stx}"
    elabCommand stx
    --runFrontend (processCommand stx) {} {} -- Executes the parsed command
  | Except.error err => IO.println s!"Parse error: {err}"


syntax (name := derivegenerator) "#derive_generator" term "with_name" term "backtrack" num: command

@[command_elab derivegenerator]
def elabDeriveGenerator : CommandElab := fun stx => do
  match stx with
  | `(#derive_generator $t with_name $t2:term backtrack $t3) =>
      let mc_block ← Command.liftTermElabM do
        let e ←  elabTerm t none
        let inpname ← termToStringList t2
        let relation ←  extract_IR_info_with_inpname e inpname
        let btnum := TSyntax.getNat t3
        get_mutual_rec_block relation inpname btnum
      parseFunction mc_block
  | _ => throwError "Invalid syntax"


#derive_generator balanced with_name ["h", "T"] backtrack 100

#eval gen_balanced_at_1 2 1


def get_enumerator (r: IR_info) (inpname: List String) (genpos: Nat) (iternum: Nat): MetaM String := do
  let gen_prototype ←  prototype_for_producer r inpname genpos
  let prototype := "enumerate" ++ ⟨gen_prototype.data.drop 3⟩
  let mut body := "let mut out:= [] "
  body := body ++ "for _i in [0:" ++ toString iternum ++ "] do \n"
  body := body ++ "let g ← gen_" ++ r.name.toString ++ "_at_" ++ toString genpos
  for inp in inpname do
    body :=  body  ++ inp ++ " "
  body := body ++ "\nreturn out"
  return prototype ++ "\n" ++ body



end Plausible.IR
