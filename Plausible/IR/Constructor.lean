import Lean
import Std
import Plausible.IR.Examples
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

/-- Datatype representing an ordered collection of `Action`s, sorted according to
    which constructor was used to create each `Action`
    - Note: `GroupedActions` was previously called `GenCheckCall_group` -/
structure GroupedActions where
  gen_list: Array Action

  /-- `iflet_list` is the list of `if let ...` expressions -/
  iflet_list : Array Action

  /-- An array of `Action`s where all of them are created using the `checkInductive` constructor -/
  checkInductiveActions: Array Action

  /-- An array of `Action`s where all of them are created using the `checkNonInductive` constructor -/
  checkNonInductiveActions: Array Action

  /-- `ret_list` is the `Action`s which are all of the form `return e` -/
  ret_list : Array Action

  variableEqualities : Array (FVarId × FVarId)

  deriving Repr

-- Pretty print `GroupedActions`s using the `MessageData` typeclass
instance : ToMessageData GroupedActions where
  toMessageData groupedActions :=
    let fields := [
      m!"gen_list := {indentD $ toMessageData groupedActions.gen_list}",
      m!"iflet_list := {indentD $ toMessageData groupedActions.iflet_list}",
      m!"checkInductiveActions := {indentD $ toMessageData groupedActions.checkInductiveActions}",
      m!"checkNonInductiveActions := {indentD $ toMessageData groupedActions.checkNonInductiveActions}",
      m!"ret_list := {indentD $ toMessageData groupedActions.ret_list}",
      m!"variableEqualities := {repr groupedActions.variableEqualities}",
    ]
    .bracket "{" (.ofList fields) "}"

/-- Determines whether a generator is to be invoked during the base case when `size == 0` (`BaseGenerator`),
    or if it is inductively-defined (`InductiveGenerator`) and to be invoked when `size > 0` -/
inductive GeneratorSort where
  | BaseGenerator
  | InductiveGenerator
  deriving Repr, BEq

/-- Determines whether a checker is to be invoked during the base case when `size == 0` (`BaseChecker`),
    or if it is inductively-defined (`InductiveChecker`) and to be invoked when `size > 0`
    - We define `CheckerSort` as a separate datatype to avoid confusing it with `GeneratorSort` -/
inductive CheckerSort where
  | BaseChecker
  | InductiveChecker
  deriving Repr, BEq

/-- Datatype containing metadata needed to derive a handler
    (handlers are a generalization of sub-generators/sub-checkers)
    - See the `SubGeneratorInfo` & `SubCheckerInfo` types, which extend this type
      with extra fields -/
structure HandlerInfo where
  /-- Argument names for each sub-generator / sub-checker -/
  inputs : Array String

  /-- Arguments that should be matched in the outer-most
      pattern match in the backtrack element
      (note that the input is the scrutinee for the match expression)
      - Invariant: `matchCases.length == inputsToMatch.length` -/
  inputsToMatch : Array String

  /-- Cases (LHS) of the pattern match mentioned above
    - The RHS of each case should be the derived generator
    - Invariant: `matchCases.length == inputsToMatch.length` -/
  matchCases : Array Expr

  /-- `groupedActions` is used to create the RHS of the first case
      in the pattern match -/
  groupedActions : GroupedActions

  /-- A list of equalities that must hold between free variables
      (used when rewriting free variabels in patterns) -/
  variableEqualities : Array (FVarId × FVarId)
  deriving Repr

/-- Datatype containing metadata needed to derive a sub-generator
    that is invoked from the main generator function
    - Note: this type was previously called `BacktrackElem` -/
structure SubGeneratorInfo extends HandlerInfo where
  /-- `generatorSort` determines if the generator is a base generator
      or is inductively defined -/
  generatorSort : GeneratorSort
  deriving Repr

/-- Datatype containing metadata needed to derive a sub-checker
    that is invoked from the main checker function -/
structure SubCheckerInfo extends HandlerInfo where
  checkerSort : CheckerSort
  deriving Repr

-- Pretty print using the `MessageData` typeclass
instance : ToMessageData HandlerInfo where
  toMessageData handlerInfo : MessageData :=
    let fields := [
      m!"inputs := {toMessageData handlerInfo.inputs}",
      m!"inputsToMatch := {toMessageData handlerInfo.inputsToMatch}",
      m!"matchCases := {indentD $ toMessageData handlerInfo.matchCases}",
      m!"actions := {indentD $ toMessageData handlerInfo.groupedActions}",
      m!"variableEqualities := {repr handlerInfo.variableEqualities}",
    ]
    .bracket "{" (.ofList fields) "}"


-- Pretty printer for `SubGeneratorInfo`
instance : ToMessageData SubGeneratorInfo where
  toMessageData subGen : MessageData :=
    .joinSep [
      toMessageData subGen.toHandlerInfo,
      m!"generatorSort := {repr subGen.generatorSort}"
    ] "¬"

-- Pretty printer for `SubCheckerInfo`
instance : ToMessageData SubCheckerInfo where
  toMessageData subChecker : MessageData :=
    .joinSep [
      toMessageData subChecker.toHandlerInfo,
      m!"checkerSort := {repr subChecker.checkerSort}"
    ] "\n"


/-- Converts an array of `Action`s into a `GroupedActions` -/
def mkGroupedActions (gccs: Array Action) : MetaM GroupedActions := do
  let mut gen_list := #[]
  let mut checkInductiveActions := #[]
  let mut checkNonInductiveActions := #[]
  let mut iflet_list := #[]
  let mut ret_list := #[]
  let mut variableEqualities : Array (FVarId × FVarId) := #[]
  for gcc in gccs do
    match gcc with
    | .genFVar _ _
    | .genInputForInductive _ _ _ _ =>
        gen_list := gen_list.push gcc
    | .matchFVar _ hyp => {
        iflet_list := iflet_list.push gcc;
        gen_list := gen_list.push gcc;
        variableEqualities := variableEqualities ++ hyp.variableEqualities;
      }
    | .ret _ =>
        ret_list := ret_list.push gcc
    | .checkInductive _ =>
        checkInductiveActions := checkInductiveActions.push gcc
    | .checkNonInductive _ =>
        checkNonInductiveActions := checkNonInductiveActions.push gcc
  return {
    gen_list := gen_list
    checkInductiveActions := checkInductiveActions
    checkNonInductiveActions := checkNonInductiveActions
    iflet_list := iflet_list
    ret_list := ret_list
    variableEqualities := variableEqualities
  }

/-- Takes a constructor for an inductive relation and a list of argument names,
    and returns a corresponding `SubCheckerInfo` for a checker -/
def mkSubCheckerInfoFromConstructor (ctor : InductiveConstructor)
  (inputNames : Array String) : MetaM SubCheckerInfo := do
  let conclusion ← separateFVars ctor.conclusion
  let args := conclusion.newHypothesis.getAppArgs
  let inputNamesAndArgs := inputNames.zip args
  let inputPairsThatNeedMatching := inputNamesAndArgs.filter (fun (_, arg) => !arg.isFVar)
  let (inputsToMatch, matchCases) := inputPairsThatNeedMatching.unzip
  let actions ← Actions_for_checker ctor
  let groupedActions ← mkGroupedActions actions
  let checkerSort := if ctor.recursive_hypotheses.isEmpty then .BaseChecker else .InductiveChecker
  return {
    inputs := inputNames
    inputsToMatch := inputsToMatch
    matchCases := matchCases
    groupedActions := groupedActions
    variableEqualities := conclusion.variableEqualities ++ groupedActions.variableEqualities
    checkerSort := checkerSort
  }

-- The functions below create strings containing Lean code based on the information
-- in a `BacktrackElement`
-- TODO: rewrite to use `TSyntax`

def add_size_param (hyp : Expr) : MetaM String := do
  let fnname := toString (← Meta.ppExpr hyp.getAppFn)
  let arg_str := (toString (← Meta.ppExpr hyp)).drop (fnname.length)
  return fnname ++ " size" ++ arg_str

def genInputForInductiveToCode (fvar : FVarId) (hyp : Expr) (idx : Nat)  : MetaM String := do
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
    a `Action` -/
def actionToCode (Action : Action) (monad: String := "IO") : MetaM String := do
  match Action with
  | .checkInductive hyp => return  "← check_" ++ (← add_size_param hyp)
  | .checkNonInductive hyp => return  "(" ++ toString (← Meta.ppExpr hyp) ++ ")"
  | .genInputForInductive fvar hyp pos _ => genInputForInductiveToCode fvar hyp pos
  | .matchFVar fvar hyp => return  "if let " ++ toString (← Meta.ppExpr hyp.newHypothesis) ++ " := " ++ toString (fvar.name) ++ " then "
  | .genFVar fvar ty =>  gen_nonIR_toCode fvar ty monad
  | .ret e => return "return " ++ (if monad = "IO" then "" else "some ") ++ toString (← Meta.ppExpr e)

/-- Produces the outer-most pattern-match block in a sub-generator
    based on the info in a `BacktrackElem` -/
def backtrackElem_match_block (backtrackElem : HandlerInfo) : MetaM String := do
  let mut out := ""
  if backtrackElem.inputsToMatch.size > 0 then
    out := out ++ "match "
    for i in backtrackElem.inputsToMatch do
      out := out ++  i  ++ " , "
    out := ⟨out.data.dropLast.dropLast⟩ ++ " with \n| "
    for a in backtrackElem.matchCases do
      out := out ++ toString (← Meta.ppExpr a) ++ " , "
    out := ⟨out.data.dropLast.dropLast⟩ ++ " =>  "
  return out

/-- Produces expressions that invoke generators in a sub-generator
  - `out` is the block of code that includes all the `gen` function calls
  - `iden` (indentation) is a string containing whitespace to make the indentation right
  - Note: this subsumes both `gen_IR` and `gen_nonIR`
-/
def backtrackElem_gen_block (backtrackElem : HandlerInfo) (monad: String :="IO"): MetaM (String × String) := do
  let mut out := ""
  let mut indentation := ""
  for action in backtrackElem.groupedActions.gen_list do
    out := out ++ indentation ++ (← actionToCode action monad) ++ " \n"
    match action with
    | .matchFVar _ _ =>
        indentation := indentation ++ " "
    | _ => continue
  if backtrackElem.groupedActions.gen_list.size > 0 then
    out := ⟨out.data.dropLast.dropLast⟩
  return (out, indentation)


/-- Produces the assignments of the results of the checker to auxiliary free variables
    ```
    let check1 <- check bst lo x
    ```
 -/
def backtrackElem_gen_check_IR_block (backtrackElem : HandlerInfo) (indentation : String) (monad: String :="IO"): MetaM (String × (List String)) := do
  let mut out := ""
  let mut vars : List String := []
  let mut checkcount := 1
  for gcc in backtrackElem.groupedActions.checkInductiveActions do
    out := out ++ indentation ++ "let check" ++ toString checkcount ++ " " ++ (← actionToCode gcc monad) ++ " \n"
    vars := vars ++ [toString checkcount]
    checkcount := checkcount + 1
  if backtrackElem.groupedActions.checkInductiveActions.size > 0 then
    out := ⟨out.data.dropLast.dropLast⟩
  return (out, vars)

def backtrackElem_return_checker (backtrackElem : HandlerInfo) (indentation : String) (vars : List String) (monad: String :="IO"): MetaM String := do
  let mut out := ""
  if backtrackElem.variableEqualities.size + backtrackElem.groupedActions.checkNonInductiveActions.size + backtrackElem.groupedActions.checkInductiveActions.size > 0 then
    out := out ++ indentation ++ "return "
  else
    out := out ++ "return true"
  for v in vars do
    out := out ++ "check" ++ v ++ " && "
  for i in backtrackElem.variableEqualities do
    out := out ++  "(" ++ toString (i.1.name) ++ " == " ++ toString (i.2.name) ++ ") && "
  for gcc in backtrackElem.groupedActions.checkNonInductiveActions do
    out := out ++ (← actionToCode gcc monad) ++ " && "
  if backtrackElem.variableEqualities.size + backtrackElem.groupedActions.checkNonInductiveActions.size + backtrackElem.groupedActions.checkInductiveActions.size > 0 then
    out := ⟨out.data.dropLast.dropLast.dropLast⟩
  if backtrackElem.groupedActions.iflet_list.size > 0 then
      out := out ++ "\nreturn false"
  if backtrackElem.inputsToMatch.size > 0 then
    out := out ++ "\n| " ++ makeUnderscores_commas backtrackElem.inputsToMatch.size ++ " => return false"
  return out

/-- Assembles all the components of a sub-checker (a `BacktrackElem`) together, returning a string
    containing the Lean code for the sub-checker -/
def backtrack_elem_toString_checker (subChecker: SubCheckerInfo) (monad: String :="IO") : MetaM String := do
  let handlerInfo := subChecker.toHandlerInfo

  IO.println "********************"
  IO.println s!"entered `backtrack_elem_toString_checker`:"
  IO.println (← MessageData.toString (toMessageData handlerInfo))

  let mut out := ""
  let matchblock ← backtrackElem_match_block handlerInfo
  let (genblock, iden) ← backtrackElem_gen_block handlerInfo monad
  let (checkIRblock, vars) ← backtrackElem_gen_check_IR_block handlerInfo iden monad
  let returnblock ← backtrackElem_return_checker handlerInfo iden vars monad
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
    let bt ← mkSubCheckerInfoFromConstructor con inpname.toArray
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



/-- Takes a constructor for an inductive relation, a list of argument names,
    the index of the argument we wish to generate (`idx`),
    and returns a corresponding `SubGeneratorInfo` for a generator -/
def mkSubGeneratorInfoFromConstructor (ctor : InductiveConstructor) (inputNames : Array String)
  (idx : Nat) : MetaM SubGeneratorInfo := do
  let inputNamesList := inputNames.toList
  let tempFVar := Expr.fvar (FVarId.mk (Name.mkStr1 "temp000"))
  let conclusion_args := ctor.conclusion.getAppArgs.set! idx tempFVar
  let new_conclusion := mkAppN ctor.conclusion.getAppFn conclusion_args
  let conclusion ← separateFVars new_conclusion
  let args := conclusion.newHypothesis.getAppArgs.toList
  let zippedInputsAndArgs := List.zip inputNamesList args

  -- Take all elements of `inputNamesAndArgs`, but omit the element at the `genpos`-th index
  let inputNamesAndArgs := List.eraseIdx zippedInputsAndArgs idx

  -- Find all pairs where the argument is not a free variable
  -- (these are the arguments that need matching)
  let inputPairsThatNeedMatching := inputNamesAndArgs.filter (fun (_, arg) => !arg.isFVar)
  let (inputsToMatch, matchCases) := inputPairsThatNeedMatching.unzip
  let actions ← Actions_for_producer ctor idx
  let groupedActions ← mkGroupedActions actions

  -- Constructors with no hypotheses get `BaseGenerator`s
  -- (otherwise, the generator needs to make a recursive call and is thus inductively-defined)
  let generatorSort := if ctor.recursive_hypotheses.isEmpty then .BaseGenerator else .InductiveGenerator

  logWarning "*******************************"
  logWarning m!"inputsToMatch = {inputsToMatch}"
  logWarning m!"matchCases = {matchCases}"
  logWarning "*******************************"

  return {
    inputs := (List.eraseIdx inputNamesList idx).toArray
    inputsToMatch := inputsToMatch.toArray
    matchCases := matchCases.toArray
    groupedActions := groupedActions
    variableEqualities := conclusion.variableEqualities ++ groupedActions.variableEqualities
    generatorSort := generatorSort
  }

/-- Produces the final if-statement that checks the conjunction of all the hypotheses
    - `vars` is a list of free variables that were produced during the `check_IR` block
    - e.g. `vars = ["1", "2", ...]`
-/
def backtrackElem_if_return_producer (subGeneratorInfo : SubGeneratorInfo) (indentation : String) (vars: List String) (monad: String :="IO"): MetaM String := do
  logWarning "inside backtrackElem_if_return_producer"
  -- logWarning m!"subGeneratorInfo = {subGeneratorInfo}"

  let mut out := ""
  if subGeneratorInfo.variableEqualities.size + subGeneratorInfo.groupedActions.checkNonInductiveActions.size + subGeneratorInfo.groupedActions.checkInductiveActions.size > 0 then
    out := out ++ indentation ++ "if "
  for j in vars do
    out := out ++ "check" ++ j ++ " && "
  for i in subGeneratorInfo.variableEqualities do
    out := out ++  "(" ++ toString (i.1.name) ++ " == " ++ toString (i.2.name) ++ ") && "
  for gcc in subGeneratorInfo.groupedActions.checkNonInductiveActions do
    out := out ++ (← actionToCode gcc monad) ++ " && "
  if subGeneratorInfo.variableEqualities.size + subGeneratorInfo.groupedActions.checkNonInductiveActions.size + subGeneratorInfo.groupedActions.checkInductiveActions.size > 0 then
    out := ⟨out.data.dropLast.dropLast.dropLast⟩ ++ "\n" ++ indentation ++  "then "
  for gcc in subGeneratorInfo.groupedActions.ret_list do
    out := out ++ indentation ++ (← actionToCode gcc monad)
  if subGeneratorInfo.variableEqualities.size + subGeneratorInfo.groupedActions.checkNonInductiveActions.size + subGeneratorInfo.groupedActions.checkInductiveActions.size + subGeneratorInfo.groupedActions.iflet_list.size > 0 then
    let monad_fail := if monad = "IO" then "throw (IO.userError \"fail at checkstep\")" else "return none"
    out := out ++ "\n" ++ monad_fail
  if subGeneratorInfo.inputsToMatch.size > 0 then
    let monad_fail := if monad = "IO" then "throw (IO.userError \"fail\")" else "return none"
    out := out ++ "\n| " ++ makeUnderscores_commas subGeneratorInfo.inputsToMatch.size ++ " => " ++ monad_fail

  return out

/-- Assembles all the components of a sub-generator (a `BacktrackElem`) together, returning a string
    containing the Lean code for the sub-generator -/
def subGeneratorInfoToString (subGen : SubGeneratorInfo) (monad: String :="IO"): MetaM String := do
  let handlerInfo := subGen.toHandlerInfo

  let mut out := ""
  let matchblock ← backtrackElem_match_block handlerInfo
  let (genblock, iden) ← backtrackElem_gen_block handlerInfo monad
  let (checkIRblock, vars) ← backtrackElem_gen_check_IR_block handlerInfo iden monad
  let returnblock ← backtrackElem_if_return_producer subGen iden vars monad
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
    let bt ← mkSubGeneratorInfoFromConstructor ctor inpname.toArray genpos
    let btStr ← subGeneratorInfoToString bt monad
    out_str:= out_str ++ btStr ++ "\n"
  return out_str

/-- Takes an `Expr` representing an inductive relation, a list of names (arguments to the inductive relation),
    and the index of the argument we wish to generate (`targetIdx`),
    and returns a collection of `SubGeneratorInfo`s for a generator -/
def getSubGeneratorInfos (inductiveRelation : Expr) (argNames : Array String) (targetIdx: Nat) : MetaM (Array SubGeneratorInfo) := do
  let inductiveInfo ← getInductiveInfoWithArgs inductiveRelation argNames
  let mut subGenerators := #[]
  for ctor in inductiveInfo.constructors do
    let subGenerator ← mkSubGeneratorInfoFromConstructor ctor argNames targetIdx
    subGenerators := subGenerators.push subGenerator
  return subGenerators

/-- Takes an `Expr` representing an inductive relation and a list of names (arguments to the inductive relation),
    and returns a collection of `BacktrackElem`s for a checker -/
def getSubCheckerInfos (inductiveRelation : Expr) (argNames : Array String) : MetaM (Array SubCheckerInfo) := do
  let inductiveInfo ← getInductiveInfoWithArgs inductiveRelation argNames
  let mut subCheckers := #[]
  for ctor in inductiveInfo.constructors do
    let subChecker ← mkSubCheckerInfoFromConstructor ctor argNames
    subCheckers := subCheckers.push subChecker
  return subCheckers


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
