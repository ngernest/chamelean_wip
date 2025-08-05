import Lean.Expr
import Batteries
import Plausible.IR.Examples
import Plausible.New.Utils
import Plausible.GeneratingGoodGenerators.Schedules
import Plausible.GeneratingGoodGenerators.UnificationMonad

open Lean Meta
open Plausible.IR

/-- Helper function for splitting a list of triples into a triple of lists -/
def splitThreeLists (abcs : List (α × β × γ)) : List α × List β × List γ :=
  match abcs with
  | [] => ([], [], [])
  | (a,b,c) :: xs =>
    let (as, bs, cs) := splitThreeLists xs
    (a::as, b::bs, c::cs)

/-- Extracts all the unique variable names that appear in a hypothesis of a constructor for an inductive relation
    (this looks underneath constructor applications).

    For example, given `typing Γ (type.Abs τ1 e) (type.Fun τ1 τ2)`,
    this function returns `[Γ, τ1, e, τ2]`.
 -/
partial def variablesInHypothesisTSyntax (term : TSyntax `term) : MetaM (List Name) :=
  match term with
  | `($id:ident) => return [id.getId.eraseMacroScopes]
  | `($_:ident $args:term*)
  | `(($_:ident $args*)) => do
    -- Note that we have to explicitly pattern match on parenthesized constructor applications,
    -- otherwise we won't be able to handle nested constructor applications, e.g. `typing Γ (type.Abs τ1 e) (type.Fun τ1 τ2)`
    let foo ← args.toList.flatMapM variablesInHypothesisTSyntax
    return (List.eraseDups foo)
  | _ => return []

/-- Extracts all the unique variable names that appear in a `ConstructorExpr`
    (this looks underneath constructor applications). -/
def variablesInConstructorExpr (ctorExpr : ConstructorExpr) : List Name :=
  match ctorExpr with
  | .Unknown u => [u]
  | .Ctor _ args => List.eraseDups $ args.flatMap variablesInConstructorExpr

/-- Given a hypothesis `hyp`, along with `binding` (a list of variables that we are binding with a call to a generator), plus `recCall` (a pair contianing the name of the inductive and a list of output argument indices),
    this function checks whether the generator we're using is recursive.

    For example, if we're trying to produce a call to the generator [(e, tau) <- typing gamma _ _], then
    we would have `binding = [e,tau]` and `hyp = typing gamma e tau`. -/
def isRecCall (binding : List Name) (hyp : HypothesisExpr) (recCall : Name × List Nat) : MetaM Bool := do
  let (ctorName, args) := hyp
  -- An output position is a position where all vars contained are unbound
  -- if they are unbound, we include them in the list of output indices (`outputPositions`)
  let outputPositions ← filterMapMWithIndex (fun i arg => do
    let vars := variablesInConstructorExpr arg
    if vars.isEmpty then pure none
    else if List.all vars (. ∈ binding) then
      pure (some i)
    else if List.any vars (. ∈ binding) then do
      let v := List.find? (· ∈ binding) vars
      logError m!"error: {v} ∈ {binding} = binding"
      throwError m!"Arguments to hypothesis {hyp} contain both fixed and yet-to-be-bound variables (not allowed)"
    else pure none) args
  let (inductiveName, outputIdxes) := recCall
  let result := (ctorName == inductiveName && List.mergeSort outputIdxes == List.mergeSort outputPositions)
  -- if not result then
  --   logWarning m!"isRecCall result = {result}"
  --   logWarning m!"isRecCall: ctorName = {ctorName}, inductiveName = {inductiveName}"
  --   logWarning m!"isRecCall: outputIdxes = {List.mergeSort outputIdxes}, outputPositions = {List.mergeSort outputPositions}"
  return result

/-- Given a list of `hypotheses`, creates an association list mapping each hypothesis to a list of variable names.
    This list is then sorted in ascending order based on the length of the variable name list.
    (This is a heuristic, since we would like to work w/ hypotheses that have fewer variables first (fewer generation options to deal with).) -/
def mkSortedHypothesesVariablesMap (hypotheses : List HypothesisExpr) : List (HypothesisExpr × List Name) :=
  let hypVarMap := hypotheses.map (fun h@(_, ctorArgs) =>
    (h, ctorArgs.flatMap variablesInConstructorExpr))
  List.mergeSort hypVarMap (le := fun (_, vars1) (_, vars2) => vars1.length <= vars2.length)

/-- Environment for the `ScheduleM` reader monad -/
structure ScheduleEnv where
  /-- List of variables which are universally-quantified in the constructor's type,
      along with the types of these variables -/
  vars : List (Name × Expr)

  /-- Hypotheses about the variables in `vars` -/
  sortedHypotheses : List (HypothesisExpr × List Name)

  /-- Determines whether we're deriving a checker/enumerator/generator -/
  deriveSort : DeriveSort

  /-- The sort of auxiliary producer (generators / enumerators) invoked by
      the function being derived. Note that if `deriveSort = Checker`, then
      `prodSort = Enumerator`, since checkers have to invoke enumerators
      as discussed in the Computing Correctly paper. -/
  prodSort : ProducerSort

  /-- A pair contianing the name of the inductive relation and a list of indices for output arguments -/
  recCall : Name × List Nat

  /-- A list of fixed variables (i.e. inputs to the inductive relation) -/
  fixed : List Name

/-- A monad for deriving generator schedules. Under the hood,
    `ScheduleM` is just a reader monad stacked on top of `MetaM`,
    with `ScheduleEnv` serving as the environment for the reader monad. -/
abbrev ScheduleM (α : Type) := ReaderT ScheduleEnv MetaM α

/-- After we generate some variables, look at the hypotheses and see if any of them only contain fixed variables
    (if yes, then we need to check that hypothesis)
    - `checkedHypotheses` contains the hypotheses that have been checked so far  -/
def collectCheckSteps (boundVars : List Name) (checkedHypotheses : List Nat) : ScheduleM (List (Nat × Source)) := do
  let env ← read
  let (inductiveName, inputArgs) := env.recCall

  let checkSteps := filterMapWithIndex (fun i (hyp, vars) =>
    if i ∉ checkedHypotheses && List.all vars (. ∈ boundVars) then
      let (ctorName, ctorArgs) := hyp
      let src :=
        if env.deriveSort == .Checker && inputArgs.isEmpty then
          if ctorName == inductiveName then .Rec `aux_dec ctorArgs
          else .NonRec hyp
        else .NonRec hyp
      some (i, src)
    else none) env.sortedHypotheses

  return checkSteps

/-- Determines whether inputs & outputs of a generator appear under the same constructor in a hypothesis `hyp`
    - Example: consider the `TApp` constructor for STLC (when we are generating `e` such that `typing Γ e τ` holds):
    ```
    | TApp: ∀ Γ e1 e2 τ1 τ2,
      typing Γ e2 τ1 →
      typing Γ e1 (.Fun τ1 τ2) →
      typing Γ (.App e1 e2) τ2
    ```
    The hypothesis `typing Γ e1 (.Fun τ1 τ2)` contains a term `.Fun τ1 τ2` where
    the existentially quantified variable `τ1` hasn't been generated yet,
    whereas `τ2` is an input to the generator (since it appears in the conclusion of `TApp`).
    Since `τ1, τ2` both appear under the same `.Fun` constructor,
    `outputInputNotUnderSameConstructor (.Fun τ1 τ2) [τ2]` returns `false`.  -/
def outputInputNotUnderSameConstructor (hyp : HypothesisExpr) (outputVars : List Name) : ScheduleM Bool := do
  let (_, args) := hyp
  let result ← not <$> args.anyM (fun arg => do
    let vars := variablesInConstructorExpr arg
    return List.any vars (. ∈ outputVars) && List.any vars (. ∉ outputVars))
  return result

/-- Determines whether the variables in `outputVars` are constrained by a function application in the hypothesis `hyp`.
    This function is necessary since we can't output something and then assert that it equals the output of a (non-constructor) function
    (since we don't have access to the function). -/
partial def outputsNotConstrainedByFunctionApplication (hyp : HypothesisExpr) (outputVars : List Name) : ScheduleM Bool :=
  let (_, args) := hyp
  not <$> args.anyM (fun arg => check false arg)
    where
      check (b : Bool) (arg : ConstructorExpr) : ScheduleM Bool :=
        match arg with
        | .Unknown u => return (b && u ∈ outputVars)
        | .Ctor ctorName args => do
          let env ← getEnv
          if env.isConstructor ctorName || (← isInductive ctorName) then
            args.anyM (check b)
          else
            args.anyM (check true)


/-- If we have a hypothesis that we're generating an argument for,
     and that argument is a constructor application where all of its args are outputs,
     then we just need to produce a backtracking check

     e.g. if we're trying to generate `TFun t1 t2 <- typing G e (TFun t1 t2)`,
     we have to do:
     ```
       v_t1t2 <- typing G e v_t1t2
       match v_t1t2 with
       | TFun t1 t2 => ...
       | _ => none
     ```
     assuming t1 and t2 are *unfixed* (not an input and not generated yet)

     The triple that is output consists of:
     - the list of pattern-matches that need to be produced
       (since TT can handle multiple outputs, each of which may need to be constrained by a pattern)
     - the updated thing we're generating for (e.g. `typing G e v_t1t2` in the example above), ie the RHS of the let-bind
     - the updated output list (e.g. `v_t1t2` in the example above), ie the LHS of the let-bind -/
def handleConstrainedOutputs (hyp : HypothesisExpr) (outputVars : List Name) : MetaM (List ScheduleStep × HypothesisExpr × List Name) := do
  let (ctorName, ctorArgs) := hyp

  let (patternMatches, args', newOutputs) ← splitThreeLists <$> ctorArgs.mapM (fun arg =>
    let vars := variablesInConstructorExpr arg
    match arg with
    | .Ctor _ _ =>
      if !vars.isEmpty && List.all vars (. ∈ outputVars) then do
        let localCtx ← getLCtx
        let newName := localCtx.getUnusedName (Name.mkStr1 ("v" ++ String.intercalate "_" (Name.getString! <$> vars)))
        let newMatch := ScheduleStep.Match newName (patternOfConstructorExpr arg)
        pure (some newMatch, .Unknown newName, some newName)
      else
        pure (none, arg, none)
    | .Unknown v =>
      if v ∈ outputVars then
        pure (none, arg, some v)
      else
        pure (none, arg, none))

  return (patternMatches.filterMap id, (ctorName, args'), newOutputs.filterMap id)

/-- Converts a list of `ScheduleStep`s to *normal form* (i.e. all unconstrained generation
    occurs before constrained generation) -/
def normalizeSchedule (steps : List ScheduleStep) : List ScheduleStep :=
  -- `unconstrainedBlock` is a list of `ScheduleStep`s consisting only of unconstrianed generation
  -- (i.e. calls to `arbitrary`)
  let rec normalize (steps : List ScheduleStep) (unconstrainedBlock : List ScheduleStep) : List ScheduleStep :=
    match steps with
    | [] =>
      -- if we run out of steps, we can just sort the `unconstrainedBlock`
      -- according to the comparison function on `scheduleStep`s
      List.mergeSort (le := compareBlocks) unconstrainedBlock
    | step@(.Unconstrained _ _ _) :: steps =>
      -- If we encounter a step consisting of unconstrained generation,
      -- we cons it onto `unconstrainedBlock` & continue
      normalize steps (step::unconstrainedBlock)
    | step :: steps =>
      -- If we encounter any step that's not unconstrained generation,
      -- the current block of unconstrained generation is over,
      -- so we need to cons it (after sorting) to the head of the list of `step` and continue
      List.mergeSort (le := compareBlocks) unconstrainedBlock ++ step :: normalize steps []
  normalize steps []
    where
      -- Comparison function on blocks of `ScheduleSteps`
      compareBlocks b1 b2 := Ordering.isLE $ Ord.compare b1 b2

/-- Depth-first enumeration of all possible schedules -/
partial def dfs (boundVars : List Name) (remainingVars : List Name) (checkedHypotheses : List Nat) (scheduleSoFar : List ScheduleStep) : ScheduleM (List (List ScheduleStep)) := do
  match remainingVars with
  | [] =>
    return [List.reverse scheduleSoFar]
  | _ => do
    let env ← read
    let unconstrainedProdPaths ←
      flatMapMWithContext remainingVars (fun v remainingVars' => do
        let (newCheckedIdxs, newCheckedHyps) ← List.unzip <$> collectCheckSteps (v::boundVars) checkedHypotheses
        let ty ← Option.getDM (List.lookup v env.vars)
          (throwError m!"key {v} missing from association list {env.vars}")
        let (ctorName, ctorArgs) := ty.getAppFnArgs
        let src ←
          if ctorName == Prod.fst env.recCall
            then Source.Rec `aux_arb <$> ctorArgs.toList.mapM (fun foo => exprToConstructorExpr foo)
          else
            let hypothesisExpr ← exprToHypothesisExpr ty
            match hypothesisExpr with
            | none => throwError m!"unable to convert Expr {ty} to a HypothesisExpr"
            | some hypExpr => pure (Source.NonRec hypExpr)
        let unconstrainedProdStep := ScheduleStep.Unconstrained v src env.prodSort
        -- TODO: handle negated propositions in `ScheduleStep.Check`
        let checks := List.reverse $ (ScheduleStep.Check . true) <$> newCheckedHyps
        dfs (v::boundVars) remainingVars'
          (newCheckedIdxs ++ checkedHypotheses)
          (checks ++ unconstrainedProdStep :: scheduleSoFar))

    let remainingHypotheses := filterMapWithIndex (fun i hyp => if i ∈ checkedHypotheses then none else some (i, hyp)) env.sortedHypotheses

    let constrainedProdPaths ← remainingHypotheses.flatMapM (fun (i, hyp, hypVars) => do
      if (i ∈ checkedHypotheses) then
        pure []
      else
        let remainingVarsSet := NameSet.ofList remainingVars
        let hypVarsSet := NameSet.ofList hypVars
        let outputSet := remainingVarsSet ∩ hypVarsSet
        let remainingVars' := (remainingVarsSet \ outputSet).toList
        let outputVars := outputSet.toList

        if outputVars.isEmpty
          || (← not <$> outputInputNotUnderSameConstructor hyp outputVars)
          || (← not <$> outputsNotConstrainedByFunctionApplication hyp outputVars) then
          pure []
        else
          let (newMatches, hyp', newOutputs) ← handleConstrainedOutputs hyp outputVars
          let typedOutputs ← newOutputs.mapM
            (fun v => do
              let tyExpr ← Option.getDM (List.lookup v env.vars)
                (throwError m!"key {v} missing from association list {env.vars}")
              let constructorExpr ← exprToConstructorExpr tyExpr
              pure (v, constructorExpr))
          let (_, hypArgs) := hyp'

          let constrainingRelation ←
            if (← isRecCall outputVars hyp env.recCall) then
              let inputArgs := filterWithIndex (fun i _ => i ∉ (Prod.snd env.recCall)) hypArgs
              pure (Source.Rec `aux_arb inputArgs)
            else
              pure (Source.NonRec hyp')
          let constrainedProdStep := ScheduleStep.SuchThat typedOutputs constrainingRelation env.prodSort

          let (newCheckedIdxs, newCheckedHyps) ← List.unzip <$> collectCheckSteps (outputVars ++ boundVars) (i::checkedHypotheses)
          -- TODO: handle negated propositions in `ScheduleStep.Check`
          let checks := List.reverse $ (ScheduleStep.Check . true) <$> newCheckedHyps

          dfs (outputVars ++ boundVars) remainingVars'
            (i :: newCheckedIdxs ++ checkedHypotheses)
            (checks ++ newMatches ++ constrainedProdStep :: scheduleSoFar))

    return constrainedProdPaths ++ unconstrainedProdPaths



/-- Computes all possible schedules for a constructor
    (each candidate schedule is represented as a `List ScheduleStep`).

    Arguments:
    - `vars`: list of universally-quantified variables and their types
    - `hypotheses`: List of hypotheses about the variables in `vars`
    - `deriveSort` determines whether we're deriving a checker/enumerator/generator
    - `recCall`: a pair contianing the name of the inductive relation and a list of indices for output arguments
      + `recCall` represents what a recursive call to the function being derived looks like
    - `fixedVars`: A list of fixed variables (i.e. inputs to the inductive relation) -/
def possibleSchedules (vars : List (Name × Expr)) (hypotheses : List HypothesisExpr) (deriveSort : DeriveSort)
  (recCall : Name × List Nat) (fixedVars : List Name) : MetaM (List (List ScheduleStep)) := do

  let sortedHypotheses := mkSortedHypothesesVariablesMap hypotheses

  let prodSort :=
    match deriveSort with
    | .Checker | .Enumerator => ProducerSort.Enumerator
    | .Generator | .Theorem => ProducerSort.Generator

  let scheduleEnv := ⟨ vars, sortedHypotheses, deriveSort, prodSort, recCall, fixedVars ⟩

  let remainingVars := List.filter (. ∉ fixedVars) (Prod.fst <$> vars)

  let (newCheckedIdxs, newCheckedHyps) ← List.unzip <$> ReaderT.run (collectCheckSteps fixedVars []) scheduleEnv
  let firstChecks := List.reverse $ (ScheduleStep.Check . true) <$> newCheckedHyps

  let schedules ← ReaderT.run (dfs fixedVars remainingVars newCheckedIdxs firstChecks) scheduleEnv

  let normalizedSchedules := List.eraseDups (normalizeSchedule <$> schedules)

  -- Keep only schedules where `SuchThat` steps only bind 1 output to the
  -- result of a call to a constrained generator
  -- (this is a simplification we make for now so we don't have to handle tupling multiple inputs to constrained generators)
  let finalSchedules := normalizedSchedules.filter
    (fun scheduleSteps =>
      scheduleSteps.all
        (fun step =>
          match step with
          | ScheduleStep.SuchThat inputs _ _ => inputs.length <= 1
          | _ => true))

  return (List.mergeSort finalSchedules (le := fun s1 s2 => s1.length <= s2.length))
