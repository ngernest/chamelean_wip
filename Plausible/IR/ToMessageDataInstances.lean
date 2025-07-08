import Lean
import Plausible.IR.Extractor
import Plausible.IR.Action
import Plausible.IR.Constructor
import Plausible.New.SubGenerators
import Plausible.New.SubCheckers

open Lean Std
open Plausible.IR

/-- To pretty-print a `Action` idiomatically, we can just make it an instance
    of the `ToMessageData` typeclass, which allows us to use Lean's delaborator to pretty-print `Expr`s -/
instance : ToMessageData Action where
  toMessageData (Action : Action) : MessageData :=
    match Action with
    | .checkInductive hyp => m!"check_IR {hyp}"
    | .checkNonInductive hyp => m!"check_nonIR ({hyp})"
    | .genInputForInductive fvar hyp idx generationStyle =>
      match generationStyle with
      | .RecursiveCall =>
        let remainingArgs := (hyp.getAppArgs.eraseIdx! idx).toList
        m!"let {fvar.name} ← aux_arb size' {remainingArgs}"
      | .TypeClassResolution =>
        m!"let {fvar.name} ← ArbitrarySuchThat.arbitraryST (fun {fvar.name} => {hyp})"
    | .matchFVar fvar hypothesis => m!"if let {hypothesis.newHypothesis} := {fvar.name} then ..."
    | .genFVar fvar ty => m!"let {fvar.name} ← SampleableExt.interpSample {ty}"
    | .ret e => m!"return {e}"


/-- `ToMessageData` instance for polymorphic `HashMap`s
    where the keys implement `Repr` and the values implement `ToMessageData` -/
instance [Repr k] [BEq k] [Hashable k] [ToMessageData v]
  : ToMessageData (HashMap k v) where
  toMessageData hashMap :=
    let entries := hashMap.toList.map fun (key, val) =>
      let kMsg := .ofFormat (repr key)
      let vMsg := toMessageData val
      .compose kMsg (.compose " ↦ " vMsg)
    .bracket "{" (.ofList entries) "}"

/-- `ToMessageData` instance for pretty-printing `InductiveConstructor`s -/
instance : ToMessageData InductiveConstructor where
  toMessageData inductiveCtor :=
    let fields := [
      m!"ctorType: {indentD $ inductiveCtor.ctorType}",
      m!"bound_vars: {inductiveCtor.bound_vars}",
      m!"bound_vars_with_base_types: {inductiveCtor.bound_vars_with_base_types}",
      m!"bound_vars_with_non_base_types: {inductiveCtor.bound_vars_with_non_base_types}",
      m!"all_hypotheses: {inductiveCtor.all_hypotheses}",
      m!"recursive_hypotheses: {inductiveCtor.recursive_hypotheses}",
      m!"hypotheses_with_only_base_type_args: {inductiveCtor.hypotheses_with_only_base_type_args}",
      m!"hypotheses_that_are_inductive_applications: {inductiveCtor.hypotheses_that_are_inductive_applications}",
      m!"nonlinear_hypotheses: {inductiveCtor.nonlinear_hypotheses}",
      m!"conclusion: {inductiveCtor.conclusion}",
      m!"final_arg_in_conclusion: {inductiveCtor.final_arg_in_conclusion}",
      m!"conclusion_args: {inductiveCtor.conclusion_args}",
      m!"inputEqualities: {inductiveCtor.inputEqualities}",
      m!"baseTypeInputEqualities: {inductiveCtor.baseTypeInputEqualities}",
      m!"nonBaseTypeInputEqualities: {inductiveCtor.nonBaseTypeInputEqualities}",
      m!"name_space: {inductiveCtor.name_space}",
      m!"dependencies: {inductiveCtor.dependencies}"
    ]
    .bracket "{" (.ofList fields) "}"

/-- `ToMessageData` instance for pretty-printing `ConstructorVal`s -/
instance : ToMessageData ConstructorVal where
  toMessageData ctorVal :=
    let fields := [
      m!"name := {ctorVal.name}",
      m!"levelParams := {ctorVal.levelParams}",
      m!"type := {ctorVal.type}",
      m!"induct := {ctorVal.induct}",
      m!"cidx := {ctorVal.cidx}",
      m!"numParams := {ctorVal.numParams}",
      m!"numFields := {ctorVal.numFields}",
      m!"isUnsafe := {ctorVal.isUnsafe}"
    ]
    .bracket "{" (.ofList fields) "}"

/-- Pretty print `GroupedActions`s using the `MessageData` typeclass -/
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



instance : ToMessageData SubGeneratorInfo where
  toMessageData subGen : MessageData :=
    .joinSep [
      toMessageData subGen.toHandlerInfo,
      m!"generatorSort := {repr subGen.generatorSort}"
    ] "¬"

instance : ToMessageData SubCheckerInfo where
  toMessageData subChecker : MessageData :=
    .joinSep [
      toMessageData subChecker.toHandlerInfo,
      m!"checkerSort := {repr subChecker.checkerSort}"
    ] "\n"
