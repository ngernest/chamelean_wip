import Lean
import Batteries
import Plausible.IR.Examples
import Plausible.New.Utils
import Plausible.GeneratingGoodGenerators.Schedules
import Plausible.GeneratingGoodGenerators.UnificationMonad
import Plausible.GeneratingGoodGenerators.DeriveSubGenerator

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
    we would have `binding = [e,tau]`, `hyp = typing gamma e tau`. -/
def isRecCall (binding : List Name) (hyp : HypothesisExpr) (recCall : Name × List Nat) : MetaM Bool := do
  let (ctorName, args) := hyp
  let outputPos ← filterMapMWithIndex (fun i arg =>
    let vars := variablesInConstructorExpr arg
    if vars.isEmpty then pure none
    else if List.all vars (. ∈ binding) then pure (some i)
    else if List.any vars (. ∈ binding) then throwError m!"Arguments to hypothesis {hyp} contain both fixed and yet-to-be-bound variables (not allowed)"
    else pure none) args
  let (inductiveName, outputIdxes) := recCall
  return (ctorName == inductiveName && List.mergeSort outputIdxes == List.mergeSort outputPos)

/-- Given a list of `hypotheses`, creates an association list mapping each hypothesis to a list of variable names.
    This list is then sorted in ascending order based on the length of the variable name list.
    (This is a heuristic, since we would like to work w/ hypotheses that have fewer variables first (fewer generation options to deal with).) -/
def mkSortedHypothesesVariablesMap (hypotheses : List HypothesisExpr) : List (HypothesisExpr × List Name) :=
  let hypVarMap := hypotheses.map (fun h@(_, ctorArgs) =>
    (h, ctorArgs.flatMap variablesInConstructorExpr))
  List.mergeSort hypVarMap (le := fun (_, vars1) (_, vars2) => vars1.length <= vars2.length)

/- After we generate some variables, look at the hypotheses and see if any of them only contain fixed variables
    (if yes, then we need to check that hypothesis)
    - `checked_hypotheses` contains the hypotheses that have been checked so far  -/
def collectCheckSteps
  (boundVars : List Name)
  (checkedHypotheses : List Nat)
  (sortedHypotheses : List (HypothesisExpr × List Name))
  (deriveSort : DeriveSort)
  (recCall : Name × List Nat) : List (Nat × Source) :=
  let (inductiveName, inputArgs) := recCall
  filterMapWithIndex (fun i (hyp, vars) =>
    if i ∉ checkedHypotheses && List.all vars (. ∈ boundVars) then
      let (ctorName, ctorArgs) := hyp
      let src :=
        if deriveSort == .Checker && inputArgs.isEmpty then
          if ctorName == inductiveName then .Rec `aux_dec ctorArgs
          else .NonRec hyp
        else .NonRec hyp
      some (i, src)
    else none
  ) sortedHypotheses


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
def outputInputNotUnderSameConstructor (hyp : HypothesisExpr) (outputVars : List Name) : Bool :=
  let (_, args) := hyp
  not $ List.any args (fun arg =>
    let vars := variablesInConstructorExpr arg
    List.any vars (. ∈ outputVars) && List.any vars (. ∉ outputVars))

-- #eval outputInputNotUnderSameConstructor (`typing, [.Unknown `Γ, .Unknown `e1, .Ctor `Fun [.Unknown `τ1, .Unknown `τ2]]) [`τ2]

/-- Determines whether the variables in `outputVars` are constrained by a function application in the hypothesis `hyp`.
    This function is necessary since we can't output something and then assert that it equals the output of a (non-constructor) function
    (since we don't have access to the function). -/
partial def outputsNotConstrainedByFunctionApplication (hyp : HypothesisExpr) (outputVars : List Name) : Bool :=
  let (_, args) := hyp
  not $ List.any args (fun arg => aux false arg)
    where
      aux (b : Bool) (arg : ConstructorExpr) :=
        match arg with
        | .Unknown u => u ∈ outputVars
        | .Ctor _ args => List.any args (aux b)


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
def handleConstraintedOutputs (hyp : HypothesisExpr) (outputVars : List Name) : MetaM (List ScheduleStep × HypothesisExpr × List Name) := do
  let (ctorName, ctorArgs) := hyp

  let (patternMatches, args', newOutputs) ← splitThreeLists <$> ctorArgs.mapM (fun arg =>
    let variables := variablesInConstructorExpr arg
    match arg with
    | .Ctor _ _ =>
      if !variables.isEmpty && List.all variables (. ∈ outputVars) then do
        let localCtx ← getLCtx
        let newName := localCtx.getUnusedName (Name.mkStr1 ("v" ++ String.intercalate "_" (Name.getString! <$> variables)))
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

/-- Converts a list of `ScheduleStep`s to normal form -/
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

structure ScheduleEnv where
  vars : List (Name × Expr)
  sortedHypotheses : List (HypothesisExpr × List Name)
  deriveSort : DeriveSort
  recCall : Name × List Nat
  prodSort : ProducerSort
  fixed : List Name


abbrev DFS (α : Type) := ReaderT ScheduleEnv MetaM α

/- Depth-first enumeration of all possible schedules -/
partial def dfs
  (boundVars : List Name)
  (remainingVars : List Name)
  (checkedHypotheses : List Nat)
  (scheduleSoFar : List ScheduleStep)
  : DFS (List (List ScheduleStep)) :=
  match remainingVars with
  | [] => return [List.reverse scheduleSoFar]
  | _ => do
    let env ← read
    let unconstrainedProdPaths ←
      flatMapMWithContext remainingVars (fun v remainingVars' => do
        let (newCheckedIdxs, newCheckedHyps) :=
          List.unzip (collectCheckSteps (v::boundVars) checkedHypotheses env.sortedHypotheses env.deriveSort env.recCall)
        let ty ← Option.getDM (List.lookup v env.vars)
          (throwError m!"key {v} missing from association list {env.vars}")
        let (ctorName, ctorArgs) := ty.getAppFnArgs
        let src ←
          if ctorName == Prod.fst env.recCall
            then Source.Rec `rec <$> ctorArgs.toList.mapM (fun foo => exprToConstructorExpr foo)
          else
            let hypothesisExpr ← exprToHypothesisExpr ty
            match hypothesisExpr with
            | none => throwError m!"unable to convert Expr {ty} to a HypothesisExpr"
            | some hypExpr => pure (Source.NonRec hypExpr)
        let unconstrainedProdStep := ScheduleStep.Unconstrained v src env.prodSort
        -- TODO: handle negated propositions in `ScheduleStep.Check`
        let checks := List.reverse $ (fun src => ScheduleStep.Check src true) <$> newCheckedHyps
        dfs (v::boundVars) remainingVars'
          (newCheckedIdxs ++ checkedHypotheses)
          (checks ++ unconstrainedProdStep :: scheduleSoFar))

    let remainingHypotheses := filterMapWithIndex (fun i hyp => if i ∈ checkedHypotheses then none else some (i, hyp)) env.sortedHypotheses

    let constrainedProdPaths ← remainingHypotheses.flatMapM (fun (i, hyp, hypVars) => do
      guard (i ∉ checkedHypotheses)
      let remainingVarsSet := NameSet.ofList remainingVars
      let hypVarsSet := NameSet.ofList hypVars
      let outputSet := remainingVarsSet ∩ hypVarsSet
      let remainingVars' := (remainingVarsSet \ outputSet).toList
      let outputVars := outputSet.toList

      guard !outputVars.isEmpty
      guard (outputInputNotUnderSameConstructor hyp outputVars)
      guard (outputsNotConstrainedByFunctionApplication hyp outputVars)

      let (newMatches, hyp', newOutputs) ← handleConstraintedOutputs hyp outputVars
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
          pure (Source.Rec `rec inputArgs)
        else
          pure (Source.NonRec hyp')
      let constrainedProdStep := ScheduleStep.SuchThat typedOutputs constrainingRelation env.prodSort
      let (newCheckedIdxs, newCheckedHyps) := List.unzip $
        collectCheckSteps (outputVars ++ boundVars) (i::checkedHypotheses) env.sortedHypotheses env.deriveSort env.recCall
      -- TODO: handle negated propositions in `ScheduleStep.Check`
      let checks := List.reverse $ (fun src => ScheduleStep.Check src true) <$> newCheckedHyps

      dfs (outputVars ++ boundVars) remainingVars'
        (i :: newCheckedIdxs ++ checkedHypotheses)
        (checks ++ newMatches ++ constrainedProdStep :: scheduleSoFar))

    return constrainedProdPaths ++ unconstrainedProdPaths

/-- Computes all possible schedules -/
def possibleSchedules (vars : List (Name × Expr)) (hypotheses : List HypothesisExpr) (deriveSort : DeriveSort)
  (recCall : Name × List Nat) (prodSort : ProducerSort) (fixed : List Name) : MetaM (List (List ScheduleStep)) := do

  let sortedHypotheses := mkSortedHypothesesVariablesMap hypotheses

  let remainingVars := List.filter (. ∉ fixed) (Prod.fst <$> vars)
  let (newCheckedIdxs, newCheckedHyps) := List.unzip $
    collectCheckSteps fixed [] sortedHypotheses deriveSort recCall
  let firstChecks := List.reverse $ (fun src => ScheduleStep.Check src true) <$> newCheckedHyps

  let scheduleEnv := ⟨ vars, sortedHypotheses, deriveSort, recCall, prodSort, fixed ⟩

  let schedules ← ReaderT.run (dfs fixed remainingVars newCheckedIdxs firstChecks) scheduleEnv

  let normalizedSchedules := List.eraseDups (normalizeSchedule <$> schedules)

  return (List.mergeSort normalizedSchedules (le := fun s1 s2 => s1.length <= s2.length))
