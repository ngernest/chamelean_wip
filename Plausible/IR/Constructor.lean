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

-- Order is the same as the order of the constructors in the inductive relation
structure GenCheckCallGroup where
  gen_list: Array GenCheckCall

  /-- `iflet_list` is the list of `if let ...` expressions -/
  iflet_list : Array GenCheckCall

  check_IR_list: Array GenCheckCall

  check_nonIR_list: Array GenCheckCall

  /-- `ret_list` is the `GenCheckCall`s which are all of the form `return e` -/
  ret_list : Array GenCheckCall

  variableEqualities : Array (FVarId × FVarId)

  deriving Repr

-- Pretty print `GenCheckCallGroup`s using the `MessageData` typeclass
instance : ToMessageData GenCheckCallGroup where
  toMessageData group :=
    let fields := [
      m!"gen_list := {indentD $ toMessageData group.gen_list}",
      m!"iflet_list := {indentD $ toMessageData group.iflet_list}",
      m!"check_IR_list := {indentD $ toMessageData group.check_IR_list}",
      m!"check_nonIR_list := {indentD $ toMessageData group.check_nonIR_list}",
      m!"ret_list := {indentD $ toMessageData group.ret_list}",
      m!"variableEqualities := {repr group.variableEqualities}",
    ]
    .bracket "{" (.ofList fields) "}"


/-- The `BacktrackElem` datatype contains metadata needed to derive a "backtrack element"
    (a sub-generator that is invoked from the main generator function) -/
structure BacktrackElem where
  /-- Argument names for each sub-generator / sub-checker (backtrack elem) -/
  inputs : Array String

  /-- Arguments that should be matched in the outer-most
      pattern match in the backtrack element -/
  inputsToBeMatched : Array String

  /-- Cases (LHS) of the pattern match mentioned above -/
  exprsToBeMatched : Array Expr

  /-- `gcc_group` is used to create the RHS of the first case
      in the pattern match -/
  gcc_group : GenCheckCallGroup

  /-- A list of equalities that must hold between free variables
      (used when rewriting free variabels in patterns) -/
  variableEqualities : Array (FVarId × FVarId)

  deriving Repr

-- Pretty print `BacktrackElem`s using the `MessageData` typeclass
instance : ToMessageData BacktrackElem where
  toMessageData backtrackElem : MessageData :=
    let fields := [
      m!"inputs := {toMessageData backtrackElem.inputs}",
      m!"inputsToBeMatched := {toMessageData backtrackElem.inputsToBeMatched}",
      m!"exprsToBeMatched := {indentD $ toMessageData backtrackElem.exprsToBeMatched}",
      m!"gcc_group := {indentD $ toMessageData backtrackElem.gcc_group}",
      m!"variableEqualities := {repr backtrackElem.variableEqualities}",
    ]
    .bracket "{" (.ofList fields) "}"


/-- Converts an array of `GenCheckCall`s into a `GenCheckCall_group` -/
def GenCheckCalls_grouping (gccs: Array GenCheckCall) : MetaM GenCheckCallGroup := do
  let mut gen_list := #[]
  let mut check_IR_list := #[]
  let mut check_nonIR_list := #[]
  let mut iflet_list := #[]
  let mut ret_list := #[]
  let mut variableEqualities : Array (FVarId × FVarId) := #[]
  for gcc in gccs do
    match gcc with
    | GenCheckCall.genFVar _ _
    | GenCheckCall.gen_IR _ _ _ =>
        gen_list := gen_list.push gcc
    | GenCheckCall.matchFVar _ hyp => {
        iflet_list := iflet_list.push gcc;
        gen_list := gen_list.push gcc;
        variableEqualities := variableEqualities ++ hyp.variableEqualities;
      }
    | GenCheckCall.ret _ =>
        ret_list := ret_list.push gcc
    | GenCheckCall.check_IR _ =>
        check_IR_list := check_IR_list.push gcc
    | _ =>
        check_nonIR_list := check_nonIR_list.push gcc
  return {
    gen_list := gen_list
    check_IR_list := check_IR_list
    check_nonIR_list := check_nonIR_list
    iflet_list := iflet_list
    ret_list := ret_list
    variableEqualities := variableEqualities
  }

/-- Takes a constructor for an inductive relation, a list of argument names, the index of the argument we wish to generate (`genpos`),
    and returns a corresponding `BacktrackElem` for a checker -/
def get_checker_backtrack_elem_from_constructor (ctor : InductiveConstructor)
  (inputNames : Array String) : MetaM BacktrackElem := do
  --Get the match expr and inp
  let conclusion ← separateFVars ctor.conclusion
  let args := (conclusion.newHypothesis.getAppArgs)
  let inputNamesAndArgs := inputNames.zip args
  let inputPairsThatNeedMatching := inputNamesAndArgs.filter (fun (_, arg) => !arg.isFVar)
  let (inputsToBeMatched, exprsToBeMatched) := inputPairsThatNeedMatching.unzip
  --Get GenCheckCall
  let gccs ← GenCheckCalls_for_checker ctor
  let gcc_group ← GenCheckCalls_grouping gccs
  return {
    inputs := inputNames
    inputsToBeMatched := inputsToBeMatched
    exprsToBeMatched := exprsToBeMatched
    gcc_group := gcc_group
    variableEqualities := conclusion.variableEqualities ++ gcc_group.variableEqualities
  }

-- The functions below create strings containing Lean code based on the information
-- in a `BacktrackElement`
-- TODO: rewrite to use `TSyntax`

def add_size_param (hyp : Expr) : MetaM String := do
  let fnname := toString (← Meta.ppExpr hyp.getAppFn)
  let arg_str := (toString (← Meta.ppExpr hyp)).drop (fnname.length)
  return fnname ++ " size" ++ arg_str

def gen_IR_at_pos_toCode (fvar : FVarId) (hyp : Expr) (idx : Nat) : MetaM String := do
  let new_args := hyp.getAppArgs.eraseIdx! idx
  let mut fn_str := "gen_" ++ toString (← Meta.ppExpr hyp.getAppFn) ++ "_at_" ++ toString idx ++ " size"
  for a in new_args do
    fn_str := fn_str ++ " "
    if a.getAppArgs.size = 0 then
      fn_str := fn_str ++ toString (← Meta.ppExpr a)
    else
      fn_str := fn_str ++ "(" ++ toString (← Meta.ppExpr a) ++ ")"
  return "let " ++ toString (fvar.name)  ++ " ← " ++ fn_str

def gen_nonIR_toCode (fvar : FVarId) (ty : Expr) (monad : String :="IO") : MetaM String := do
  let mut out := "let "++ toString (fvar.name)
  let mut typename := afterLastDot (toString (← Meta.ppExpr ty))
  if typename.contains ' ' then typename:= "(" ++ typename ++ ")"
  if monad = "IO" then
    out := out ++ " ← monadLift <| Gen.run (SampleableExt.interpSample " ++ typename ++ ") 100"
  else
    out := out ++ " ←  SampleableExt.interpSample " ++ typename
  return out

/-- Produces a string containing the Lean code that corresponds to
    a `GenCheckCall` -/
def GenCheckCalls_toCode (genCheckCall : GenCheckCall) (monad: String := "IO") : MetaM String := do
  match genCheckCall with
  | .check_IR hyp => return  "← check_" ++ (← add_size_param hyp)
  | .check_nonIR hyp => return  "(" ++ toString (← Meta.ppExpr hyp) ++ ")"
  | .gen_IR fvar hyp pos => gen_IR_at_pos_toCode fvar hyp pos
  | .matchFVar fvar hyp => return  "if let " ++ toString (← Meta.ppExpr hyp.newHypothesis) ++ " := " ++ toString (fvar.name) ++ " then "
  | .genFVar fvar ty =>  gen_nonIR_toCode fvar ty monad
  | .ret e => return "return " ++ (if monad = "IO" then "" else "some ") ++ toString (← Meta.ppExpr e)

-- Produces the outer-most pattern-match block in a sub-generator
-- based on the info in a `BacktrackElem`
-- TODO: use the information from `GenCheckCall` to rpoduce the RHS of the pattern-match
def backtrackElem_match_block (backtrackElem : BacktrackElem) : MetaM String := do
  let mut out := ""
  if backtrackElem.inputsToBeMatched.size > 0 then
    out := out ++ "match "
    for i in backtrackElem.inputsToBeMatched do
      out := out ++  i  ++ " , "
    out := ⟨out.data.dropLast.dropLast⟩ ++ " with \n| "
    for a in backtrackElem.exprsToBeMatched do
      out := out ++ toString (← Meta.ppExpr a) ++ " , "
    out := ⟨out.data.dropLast.dropLast⟩ ++ " =>  "
  return out

/-- Produces expressions that invoke generators in a sub-generator
  - `out` is the block of code that includes all the `gen` function calls
  - `iden` (indentation) is a string containing whitespace to make the indentation right
  - Note: this subsumes both `gen_IR` and `gen_nonIR`
-/
def backtrackElem_gen_block (backtrackElem : BacktrackElem) (monad: String :="IO"): MetaM (String × String) := do
  let mut out := ""
  let mut iden := ""
  for gcc in backtrackElem.gcc_group.gen_list do
    out := out ++ iden ++ (← GenCheckCalls_toCode gcc monad) ++ " \n"
    match gcc with
    | .matchFVar _ _ => iden := iden ++ " "
    | _ => continue
  if backtrackElem.gcc_group.gen_list.size > 0 then
    out := ⟨out.data.dropLast.dropLast⟩
  return (out, iden)


/-- Produces the assignments of the results of the checker to auxiliary free variables
    ```
    let check1 <- check bst lo x
    ```
 -/
def backtrackElem_gen_check_IR_block (backtrackElem : BacktrackElem) (indentation : String) (monad: String :="IO"): MetaM (String × (List String)) := do
  let mut out := ""
  let mut vars : List String := []
  let mut checkcount := 1
  for gcc in backtrackElem.gcc_group.check_IR_list do
    out := out ++ indentation ++ "let check" ++ toString checkcount ++ " " ++ (← GenCheckCalls_toCode gcc monad) ++ " \n"
    vars := vars ++ [toString checkcount]
    checkcount := checkcount + 1
  if backtrackElem.gcc_group.check_IR_list.size > 0 then
    out := ⟨out.data.dropLast.dropLast⟩
  return (out, vars)

def backtrackElem_return_checker (backtrackElem : BacktrackElem) (indentation : String) (vars : List String) (monad: String :="IO"): MetaM String := do
  let mut out := ""
  if backtrackElem.variableEqualities.size + backtrackElem.gcc_group.check_nonIR_list.size + backtrackElem.gcc_group.check_IR_list.size > 0 then
    out := out ++ indentation ++ "return "
  else
    out := out ++ "return true"
  for v in vars do
    out := out ++ "check" ++ v ++ " && "
  for i in backtrackElem.variableEqualities do
    out := out ++  "(" ++ toString (i.1.name) ++ " == " ++ toString (i.2.name) ++ ") && "
  for gcc in backtrackElem.gcc_group.check_nonIR_list do
    out := out ++ (← GenCheckCalls_toCode gcc monad) ++ " && "
  if backtrackElem.variableEqualities.size + backtrackElem.gcc_group.check_nonIR_list.size + backtrackElem.gcc_group.check_IR_list.size > 0 then
    out := ⟨out.data.dropLast.dropLast.dropLast⟩
  if backtrackElem.gcc_group.iflet_list.size > 0 then
      out := out ++ "\nreturn false"
  if backtrackElem.inputsToBeMatched.size > 0 then
    out := out ++ "\n| " ++ makeUnderscores_commas backtrackElem.inputsToBeMatched.size ++ " => return false"
  return out

/-- Assembles all the components of a sub-checker (a `BacktrackElem`) together, returning a string
    containing the Lean code for the sub-checker -/
def backtrack_elem_toString_checker (backtrackElem: BacktrackElem) (monad: String :="IO") : MetaM String := do
  let mut out := ""
  let matchblock ← backtrackElem_match_block backtrackElem
  let (genblock, iden) ← backtrackElem_gen_block backtrackElem monad
  let (checkIRblock, vars) ← backtrackElem_gen_check_IR_block backtrackElem iden monad
  let returnblock ← backtrackElem_return_checker backtrackElem iden vars monad
  out := out ++ matchblock
  if genblock.length > 0 ∧ out.length > 0 then
    out := out ++ "\n"
  out := out ++ genblock
  if checkIRblock.length > 0 ∧ out.length > 0 then
    out := out ++ "\n"
  out := out ++ checkIRblock
  if genblock.length + checkIRblock.length > 0 then
    out := out ++ "\n" ++ returnblock
  else out := out ++ returnblock
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
    let bt ← get_checker_backtrack_elem_from_constructor con inpname.toArray
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

-- #get_backtrack_checker typing with_name ["L", "e", "t"]
-- #get_backtrack_checker balanced with_name ["h", "T"]
-- #get_backtrack_checker bst with_name ["lo", "hi", "T"]



-- BACKTRACK PRODUCER ---

/-- Takes a constructor for an inductive relation, a list of argument names, the index of the argument we wish to generate (`genpos`),
    and returns a corresponding `BacktrackElem` for a generator -/
def get_producer_backtrack_elem_from_constructor (ctor: InductiveConstructor) (inputNames : Array String) (genpos: Nat)
      : MetaM BacktrackElem := do
  let inputNamesList := inputNames.toList
  let tempFVar := Expr.fvar (FVarId.mk (Name.mkStr1 "temp000"))
  let conclusion_args := ctor.conclusion.getAppArgs.set! genpos tempFVar
  let new_conclusion := mkAppN ctor.conclusion.getAppFn conclusion_args
  let conclusion ← separateFVars new_conclusion
  let args := conclusion.newHypothesis.getAppArgs.toList
  let zippedInputsAndArgs := List.zip inputNamesList args
  -- Take all elements of `inputNamesAndArgs`, but omit the element at the `genpos`-th index
  let inputNamesAndArgs := List.eraseIdx zippedInputsAndArgs genpos
  -- Find all pairs where the argument is not a free variable
  -- (these are the arguments that need matching)
  let inputPairsThatNeedMatching := inputNamesAndArgs.filter (fun (_, arg) => !arg.isFVar)
  let (inputsToBeMatched, exprsToBeMatched) := inputPairsThatNeedMatching.unzip
  --Get GenCheckCall
  let gccs ← GenCheckCalls_for_producer ctor genpos
  let gcc_group ← GenCheckCalls_grouping gccs
  return {
    inputs := (List.eraseIdx inputNamesList genpos).toArray
    inputsToBeMatched := inputsToBeMatched.toArray
    exprsToBeMatched := exprsToBeMatched.toArray
    gcc_group := gcc_group
    variableEqualities := conclusion.variableEqualities ++ gcc_group.variableEqualities
  }

/-- Produces the final if-statement that checks the conjunction of all the hypotheses
    - `vars` is a list of free variables that were produced during the `check_IR` block
    - e.g. `vars = ["1", "2", ...]`
-/
def backtrackElem_if_return_producer (backtrackElem : BacktrackElem) (indentation : String) (vars: List String) (monad: String :="IO"): MetaM String := do
  let mut out := ""
  if backtrackElem.variableEqualities.size + backtrackElem.gcc_group.check_nonIR_list.size + backtrackElem.gcc_group.check_IR_list.size > 0 then
    out := out ++ indentation ++ "if "
  for j in vars do
    out := out ++ "check" ++ j ++ " && "
  for i in backtrackElem.variableEqualities do
    out := out ++  "(" ++ toString (i.1.name) ++ " == " ++ toString (i.2.name) ++ ") && "
  for gcc in backtrackElem.gcc_group.check_nonIR_list do
    out := out ++ (← GenCheckCalls_toCode gcc monad) ++ " && "
  if backtrackElem.variableEqualities.size + backtrackElem.gcc_group.check_nonIR_list.size + backtrackElem.gcc_group.check_IR_list.size > 0 then
    out := ⟨out.data.dropLast.dropLast.dropLast⟩ ++ "\n" ++ indentation ++  "then "
  for gcc in backtrackElem.gcc_group.ret_list do
    out := out ++ indentation ++ (← GenCheckCalls_toCode gcc monad)
  if backtrackElem.variableEqualities.size + backtrackElem.gcc_group.check_nonIR_list.size + backtrackElem.gcc_group.check_IR_list.size + backtrackElem.gcc_group.iflet_list.size > 0 then
    let monad_fail := if monad = "IO" then "throw (IO.userError \"fail at checkstep\")" else "return none"
    out := out ++ "\n" ++ monad_fail
  if backtrackElem.inputsToBeMatched.size > 0 then
    let monad_fail := if monad = "IO" then "throw (IO.userError \"fail\")" else "return none"
    out := out ++ "\n| " ++ makeUnderscores_commas backtrackElem.inputsToBeMatched.size ++ " => " ++ monad_fail

  IO.println "********************"
  IO.println s!"inside if_return_producer: \n{out}"

  return out

/-- Assembles all the components of a sub-generator (a `BacktrackElem`) together, returning a string
    containing the Lean code for the sub-generator -/
def backtrack_elem_toString_producer (backtrackElem : BacktrackElem) (monad: String :="IO"): MetaM String := do
  IO.println "********************"
  IO.println s!"entered `backtrack_elem_toString_producer`:"
  IO.println (← MessageData.toString (toMessageData backtrackElem))

  let mut out := ""
  let matchblock ← backtrackElem_match_block backtrackElem
  let (genblock, iden) ← backtrackElem_gen_block backtrackElem monad
  let (checkIRblock, vars) ← backtrackElem_gen_check_IR_block backtrackElem iden monad
  let returnblock ← backtrackElem_if_return_producer backtrackElem iden vars monad
  out := out ++ matchblock
  if genblock.length + checkIRblock.length + returnblock.length > 0 ∧ out.length > 0 then
    out := out ++ "\n"
  out := out ++ genblock
  if checkIRblock.length > 0 ∧ out.length > 0 then
    out := out ++ "\n"
  out := out ++ checkIRblock
  if genblock.length + checkIRblock.length > 0 then
    out := out ++ "\n" ++ returnblock
  else out := out ++ returnblock

  -- TODO: figure out how to assemble `out` using `TSyntax`es for the sub-components
  IO.println "********************"
  IO.println "back in `backtrack_elem_toString_producer`:"
  IO.println s!"out = {out}"

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
    let bt ← get_producer_backtrack_elem_from_constructor ctor inpname.toArray genpos
    let btStr ← backtrack_elem_toString_producer bt monad
    out_str:= out_str ++ btStr ++ "\n"
  return out_str

/-- Takes an `Expr` representing an inductive relation, a list of names (arguments to the inductive relation),
    and the index of the argument we wish to generate (`targetIdx`),
    and returns a collection of `BacktrackElem`s for a generator -/
def get_producer_backtrack_elems (inductiveRelation : Expr) (argNames : Array String) (targetIdx: Nat) : MetaM (Array BacktrackElem) := do
  let inductiveInfo ← getInductiveInfoWithArgs inductiveRelation argNames
  let mut output := #[]
  for ctor in inductiveInfo.constructors do
    let backtrackElem ← get_producer_backtrack_elem_from_constructor ctor argNames targetIdx
    output := output.push backtrackElem
  return output

/-- Takes an `Expr` representing an inductive relation and a list of names (arguments to the inductive relation),
    and returns a collection of `BacktrackElem`s for a checker -/
def get_checker_backtrack_elems (inductiveRelation : Expr) (argNames : Array String) : MetaM (Array BacktrackElem) := do
  let inductiveInfo ← getInductiveInfoWithArgs inductiveRelation argNames
  let mut output := #[]
  for ctor in inductiveInfo.constructors do
    let backtrackElem ← get_checker_backtrack_elem_from_constructor ctor argNames
    output := output.push backtrackElem
  return output


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

-- #get_backtrack_producer typing with_name ["L", "e", "t"] for_arg 0
-- #get_backtrack_producer typing with_name ["L", "e", "t"] for_arg 2
-- #get_backtrack_producer typing with_name ["L", "e", "t"] for_arg 1
-- #get_backtrack_producer balanced with_name ["h", "T"] for_arg 1
-- #get_backtrack_producer bst with_name ["lo", "hi", "T"] for_arg 2


end Plausible.IR
