import Lean
import Std
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


namespace Plausible.IR
-- Generate function --


def get_checker (r: InductiveInfo) (inpname: List String) (btnum: Nat)
    (monad: String :="IO") : MetaM String := do
  let prototype ← prototype_for_checker r inpname monad
  let body ← checker_body r inpname btnum monad
  let where_def ← checker_where_defs r inpname monad
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
      let relation ← getInductiveInfoWithArgs e inpname.toArray
      logInfo s!"input variable names = {relation.input_var_names}"
      let btnum := TSyntax.getNat t3
      let checker := get_checker relation inpname btnum
      print_m_string checker
  | _ => throwError "Invalid syntax"

-- #gen_checker typing with_name ["L", "e", "t"] backtrack 100
-- #gen_checker balanced with_name ["h", "T"] backtrack 100
-- #gen_checker bst with_name ["lo", "hi", "T"] backtrack 100

def get_producer (inductiveInfo : InductiveInfo) (arg_names : List String) (genpos: Nat) (btnum: Nat)
    (monad: String :="IO") : MetaM String := do
  let prototype ← prototype_for_producer inductiveInfo arg_names genpos monad
  let body ← producer_body inductiveInfo arg_names genpos btnum monad
  let where_def ← producer_where_defs inductiveInfo arg_names genpos monad
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
      let inductiveInfo ← getInductiveInfoWithArgs e inpname.toArray
      let pos := TSyntax.getNat t3
      let btnum := TSyntax.getNat t4
      let producer := get_producer inductiveInfo inpname pos btnum
      print_m_string producer
  | _ => throwError "Invalid syntax"

-- #gen_producer typing with_name ["L", "e", "t"] for_arg 2 backtrack 100
-- #gen_producer balanced with_name ["h", "T"] for_arg 1 backtrack 100

#gen_producer bst with_name ["lo", "hi", "T"] for_arg 2 backtrack 100


def get_mutual_rec_block (r: InductiveInfo) (inpname: List String) (btnum: Nat) (monad: String :="IO"): MetaM String := do
  let checker ←  get_checker r inpname btnum monad
  let mut mc_block := "mutual\n-- CHECKER \n " ++ checker
  for pos in [0:r.input_types.size] do
    let producer ← get_producer r inpname pos btnum monad
    mc_block := mc_block ++ "\n-- GENERATOR FOR ARG" ++ toString pos ++ "\n" ++ producer
  mc_block := mc_block ++ "\nend"
  return mc_block

syntax (name := genmutualrec) "#gen_mutual_rec" term "with_name" term "backtrack" num "monad" str: command

@[command_elab genmutualrec]
def elabGetMutualBlock : CommandElab := fun stx => do
  match stx with
  | `(#gen_mutual_rec $t with_name $t2:term backtrack $t3 monad $t4) =>
    Command.liftTermElabM do
      let e ← elabTerm t none
      let inpname ← termToStringList t2
      let relation ←  getInductiveInfoWithArgs e inpname.toArray
      let btnum := TSyntax.getNat t3
      let mnad := TSyntax.getString t4
      let mc_block := get_mutual_rec_block relation inpname btnum mnad
      print_m_string mc_block
  | _ => throwError "Invalid syntax"

-- #gen_mutual_rec typing with_name ["L", "e", "t"] backtrack 100 monad "IO"
-- #gen_mutual_rec typing with_name ["L", "e", "t"] backtrack 100 monad "Gen"
-- #gen_mutual_rec balanced with_name ["h", "T"] backtrack 100 monad "IO"
-- #gen_mutual_rec bst with_name ["lo", "hi", "T"] backtrack 100 monad "IO"
-- #gen_mutual_rec bst with_name ["lo", "hi", "T"] backtrack 100 monad "Gen"


def get_testfile (r: InductiveInfo) (inpname: List String) (btnum: Nat) : MetaM String := do
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
      let relation ←  getInductiveInfoWithArgs e inpname.toArray
      let btnum := TSyntax.getNat t3
      let mc_block ←  get_testfile relation inpname btnum
      let path := System.FilePath.mk "Plausible" / "TestIR" / filename
      IO.FS.writeFile path.toString mc_block
  | _ => throwError "Invalid syntax"

--#writefile_mutual_rec typing with_name ["L", "e", "t"] backtrack 100 tofile "typing.lean"
--#writefile_mutual_rec balanced with_name ["h", "T"] backtrack 100 tofile "balanced.lean"
--#writefile_mutual_rec bst with_name ["lo", "hi", "T"] backtrack 100 tofile "bst.lean"


syntax (name := derivegenerator) "#derive_generator" term "backtrack" num: command

@[command_elab derivegenerator]
def elabDeriveGenerator : CommandElab := fun stx => do
  match stx with
  | `(#derive_generator $t backtrack $t3) =>
      let mc_block ← Command.liftTermElabM do
        let e ←  elabTerm t none
        let r0 ← getInductiveInfo e
        let inpname := makeInputs "in" r0.input_types.size
        let relation ←  getInductiveInfoWithArgs e inpname.toArray
        let btnum := TSyntax.getNat t3
        get_mutual_rec_block relation inpname btnum
      parseCommand mc_block
  | _ => throwError "Invalid syntax"



def get_mutual_rec_blocks_dependencies (IR: Expr) (btnum: Nat) (mond : String:= "IO"): MetaM (Array String) := do
  let r0 ← getInductiveInfo IR
  let deps := (r0.dependencies).push IR
  let mut mc_blocks : Array String := #[]
  for dep in deps do
    let deprel0 ← getInductiveInfo dep
    --let inname := (afterLastDot dep.constName.toString) ++ "_in"
    let depinpname := makeInputs "in" deprel0.input_types.size
    let deprel ← getInductiveInfoWithArgs dep depinpname.toArray
    let mc_block ←  get_mutual_rec_block deprel depinpname btnum mond
    mc_blocks := mc_blocks.push mc_block
  return mc_blocks


syntax (name := genmutualrecdeps) "#gen_mutual_rec_deps" term  "backtrack" num "monad" str: command

@[command_elab genmutualrecdeps]
def elabGetMutualBlockdeps : CommandElab := fun stx => do
  match stx with
  | `(#gen_mutual_rec_deps $t backtrack $t3 monad $t4) =>
    Command.liftTermElabM do
      let e ← elabTerm t none
      let mnad := TSyntax.getString t4
      let btnum := TSyntax.getNat t3
      let mc_blocks := get_mutual_rec_blocks_dependencies e btnum mnad
      print_m_arr_string mc_blocks
  | _ => throwError "Invalid syntax"



syntax (name := derivegeneratordeps) "#derive_generator_with_dependencies" term "backtrack" num: command

@[command_elab derivegeneratordeps]
def elabDeriveGeneratorDep : CommandElab := fun stx => do
  match stx with
  | `(#derive_generator $t backtrack $t3) =>
      let mc_blocks ← Command.liftTermElabM do
        let e ←  elabTerm t none
        let btnum := TSyntax.getNat t3
        get_mutual_rec_blocks_dependencies e btnum
      parseCommands mc_blocks
  | _ => throwError "Invalid syntax"

def get_enumerator (r: InductiveInfo) (inpname: List String) (genpos: Nat) (iternum: Nat): MetaM String := do
  let gen_prototype ←  prototype_for_producer r inpname genpos
  let prototype := "enumerate" ++ ⟨gen_prototype.data.drop 3⟩
  let mut body := "let mut out:= [] "
  body := body ++ "for _i in [0:" ++ toString iternum ++ "] do \n"
  body := body ++ "let g ← gen_" ++ r.inductive_name.toString ++ "_at_" ++ toString genpos
  for inp in inpname do
    body :=  body  ++ inp ++ " "
  body := body ++ "\nreturn out"
  return prototype ++ "\n" ++ body

end Plausible.IR
