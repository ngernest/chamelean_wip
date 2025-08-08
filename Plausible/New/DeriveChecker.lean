import Lean
import Plausible.IR.Prelude
import Plausible.New.MakeConstrainedProducerInstance
import Plausible.New.DeriveConstrainedProducer
import Plausible.New.SubCheckers
import Plausible.New.Idents
import Plausible.New.DecOpt
import Plausible.New.UnificationMonad

open Lean Std Elab Command Meta Term Parser
open Idents
open Plausible.IR


/-- Unifies each argument in the conclusion of an inductive relation with the top-level arguments to the relation
    (using the unification algorithm from Generating Good Generations),
    and subsequently computes a *naive* checker schedule for a sub-checker corresponding to the constructor
    (using the schedules discussed in Testing Theorems).

    Note: this function processes the entire type of the constructor within the same `LocalContext`
    (the one produced by `forallTelescopeReducing`).

    This function takes the following as arguments:
    - The name of the inductive relation `inductiveName`
    - The constructor name `ctorName`
    - The names of inputs `inputNames` (arguments to the checker, i.e. all arguments to the inductive relation) -/
def getCheckerScheduleForInductiveConstructor (inductiveName : Name) (ctorName : Name)  (inputNames : List Name) : UnifyM Schedule := do
  let ctorInfo ← getConstInfoCtor ctorName
  let ctorType := ctorInfo.type

  -- Stay within the forallTelescope scope for all processing
  forallTelescopeReducing ctorType (cleanupAnnotations := true) (fun forAllVarsAndHyps conclusion => do
    -- Collect all the universally-quantified variables + hypotheses
    -- Universally-quantified variables `x : τ` are represented using `(some x, τ)`
    -- Hypotheses are represented using `(none, hyp)` (first component is `none` since a hypothesis doesn't have a name)
    let forAllVarsAndHypsWithTypes ← forAllVarsAndHyps.mapM (fun fvar => do
      let localCtx ← getLCtx
      let localDecl := localCtx.get! fvar.fvarId!
      let userName := localDecl.userName
      if not userName.hasMacroScopes then
        return (some userName, localDecl.type)
      else
        return (none, localDecl.type))

    -- Extract the universally quantified variables
    let forAllVars := forAllVarsAndHypsWithTypes.filterMap (fun (nameOpt, ty) =>
      match nameOpt with
      | some name => some (name, ty)
      | none => none) |>.toList

    -- Extract hypotheses (which correspond to pairs in `forAllVarsAndHypsWithTypes` where the first component is `none`)
    let hypotheses := forAllVarsAndHypsWithTypes.filterMap (fun (nameOpt, tyExpr) =>
      match nameOpt with
      | none => some tyExpr
      | some _ => none)

    -- Check if the conclusion contains a non-trivial function call
    -- (i.e. one where the function is not a constructor of an inductive type)
    let conclusionNeedsRewriting ← containsNonTrivialFuncApp conclusion inductiveName

    -- For each function call in the cocnlusion, rewrite it by introducing a fresh variable
    -- equal to the result of the function call, and adding an extra hypothesis asserting equality
    -- between the function call and the variable.
    -- `freshNamesAndTypes` is a list containing the names & types of the fresh variables produced during this procedure.
    let (updatedHypotheses, updatedConclusion, freshNamesAndTypes, updatedLocalCtx) ←
      if conclusionNeedsRewriting then
        rewriteFunctionCallsInConclusion hypotheses conclusion inductiveName (← getLCtx)
      else
        pure (hypotheses, conclusion, [], ← getLCtx)

    -- Enter the updated `LocalContext` containing the fresh variable that was created when rewriting the conclusion
    withLCtx' updatedLocalCtx (do
      -- Stores the representation of hypotheses as a `HypothesisExpr`
      -- (constructor name applied to some list of arguments, which are themselves `ConstructorExpr`s)
      let mut hypothesisExprs := #[]

      for hyp in updatedHypotheses do
        let hypTerm ← withOptions setDelaboratorOptions (delabExprInLocalContext updatedLocalCtx hyp)
        -- Convert the `TSyntax` representation of the hypothesis to a `Range`
        -- If that fails, convert the `Expr` representation of the hypothesis to a `Range`
        -- (the latter is needed to handle hypotheses which use infix operators)
        let hypRange ←
          try convertHypothesisTermToRange hypTerm
          catch _ => convertExprToRangeInCurrentContext hyp

        -- Convert each hypothesis' range to a `HypothesisExpr`, which is just a constructor application
        -- (constructor name applied to some list of arguments, which are themselves `ConstructorExpr`s)
        hypothesisExprs := hypothesisExprs.push (← convertRangeToCtorAppForm hypRange)

      -- Creates the initial `UnifyState` needed for the unification algorithm
      let initialUnifyState := mkCheckerInitialUnifyState inputNames forAllVars hypothesisExprs.toList

      -- Extend the current state with the contents of `initialUnifyState`
      UnifyM.extendState initialUnifyState

      -- Get the ranges corresponding to each of the inputs
      let unknownRanges ← inputNames.mapM processCorrespondingRange
      let unknownArgsAndRanges := (inputNames.zip unknownRanges).toArray

      -- Compute the appropriate `Range` for each argument in the constructor's conclusion
      let conclusionArgs := updatedConclusion.getAppArgs
      let conclusionRanges ← conclusionArgs.mapM convertExprToRangeInCurrentContext
      let conclusionArgsAndRanges := conclusionArgs.zip conclusionRanges

      for ((_u1, r1), (_u2, r2)) in conclusionArgsAndRanges.zip unknownArgsAndRanges do
        unify r1 r2

      -- Convert the conclusion from an `Expr` to a `HypothesisExpr`
      let conclusionExpr ← Option.getDM (← exprToHypothesisExpr conclusion)
        (throwError m!"Unable to convert conclusion {conclusion} to a HypothesisExpr")

      -- Determine the appropriate `ScheduleSort` (right now we only produce `ScheduleSort`s for `Generator`s)
      let scheduleSort ← getScheduleSort
        conclusionExpr
        (outputVars := [])
        (ctorNameOpt := none)
        (deriveSort := .Checker)
        (returnOption := true)

      -- Check which universally-quantified variables have a `Fixed` range,
      -- so that we can supply them to `possibleSchedules` as the `fixedVars` arg
      let fixedVars ← forAllVars.filterMapM (fun (v, _) => do
        if (← UnifyM.isUnknownFixed v) then
          return some v
        else
          return none)

      -- Include any fresh variables produced (when rewriting function calls in conclusions)
      -- in the list of universally-quantified variables
      let updatedForAllVars := forAllVars ++ freshNamesAndTypes

      -- Compute all possible checker schedules for this constructor
      let possibleSchedules ← possibleSchedules
        (vars := updatedForAllVars)
        (hypotheses := hypothesisExprs.toList)
        (deriveSort := .Checker)
        (recCall := (inductiveName, []))
        (fixedVars := fixedVars)

      -- A *naive* schedule is the first schedule contained in `possibleSchedules`
      let originalNaiveSchedule ← Option.getDM (possibleSchedules.head?) (throwError m!"Unable to compute any possible schedules")

      -- Update the naive schedule with the result of unification
      let updatedNaiveSchedule ← updateScheduleSteps originalNaiveSchedule

      let finalState ← get

      -- Takes the `patterns` and `equalities` fields from `UnifyState` (created after
      -- the conclusion of a constructor has been unified with the top-level arguments to the inductive relation),
      -- convert them to the appropriate `ScheduleStep`s, and prepends them to the `naiveSchedule`
      let fullSchedule := addConclusionPatternsAndEqualitiesToSchedule finalState.patterns finalState.equalities (updatedNaiveSchedule, scheduleSort)

      logWarning m!"checker schedule = {repr fullSchedule}"

      return fullSchedule)
  )

/-- Produces an instance of the `DecOpt` typeclass containing the definition for the top-level derived checker.
    The arguments to this function are:
    - a list of `baseCheckers` (each represented as a Lean term), to be invoked when `size == 0`
    - a list of `inductiveCheckers`, to be invoked when `size > 0`
    - the name of the inductive relation (`inductiveStx`)
    - the arguments (`args`) to the inductive relation

    - Note: this function is identical to `mkTopLevelChecker`, except it doesn't take in a `NameMap` argument
    - TODO: refactor to avoid code duplication -/
def mkTopLevelCheckerNEW (baseCheckers : TSyntax `term) (inductiveCheckers : TSyntax `term)
  (inductiveStx : TSyntax `term) (args : TSyntaxArray `term) (topLevelLocalCtx : LocalContext) : CommandElabM (TSyntax `command) := do

  -- Produce a fresh name for the `size` argument for the lambda
  -- at the end of the checker function, as well as the `aux_dec` inner helper function
  let freshSizeIdent := mkFreshAccessibleIdent topLevelLocalCtx `size
  let freshSize' := mkFreshAccessibleIdent topLevelLocalCtx `size'
  let auxDecIdent := mkFreshAccessibleIdent topLevelLocalCtx `aux_dec
  let checkerType ← `($optionTypeConstructor $boolIdent)

  let inductiveName := inductiveStx.raw.getId

  -- Create the cases for the pattern-match on the size argument
  let mut caseExprs := #[]
  let zeroCase ← `(Term.matchAltExpr| | $(mkIdent ``Nat.zero) => $checkerBacktrackFn $baseCheckers)
  caseExprs := caseExprs.push zeroCase

  let succCase ← `(Term.matchAltExpr| | $(mkIdent ``Nat.succ) $freshSize' => $checkerBacktrackFn $inductiveCheckers)
  caseExprs := caseExprs.push succCase

  -- Create function arguments for the checker's `size` & `initSize` parameters
  -- (former is the generator size, latter is the size argument with which to invoke other auxiliary generators/checkers)
  let initSizeParam ← `(Term.letIdBinder| ($initSizeIdent : $natIdent))
  let sizeParam ← `(Term.letIdBinder| ($sizeIdent : $natIdent))
  let matchExpr ← liftTermElabM $ mkMatchExpr sizeIdent caseExprs

  -- Add parameters for each argument to the inductive relation
  let paramInfo ← analyzeInductiveArgs inductiveName args

  -- Inner params are for the inner `aux_dec` function
  let mut innerParams := #[]
  innerParams := innerParams.push initSizeParam
  innerParams := innerParams.push sizeParam

  -- Outer params are for the top-level lambda function which invokes `aux_dec`
  let mut outerParams := #[]
  for (paramName, paramType) in paramInfo do
    let outerParamIdent := mkIdent paramName
    outerParams := outerParams.push outerParamIdent

    -- Inner parameters are for the inner `aux_arb` function
    let innerParam ← `(Term.letIdBinder| ($(mkIdent paramName) : $paramType))
    innerParams := innerParams.push innerParam

  -- Produces an instance of the `DecOpt` typeclass containing the definition for the derived generator
  `(instance : $decOptTypeclass ($inductiveStx $args*) where
      $unqualifiedDecOptFn:ident :=
        let rec $auxDecIdent:ident $innerParams* : $checkerType :=
          $matchExpr
        fun $freshSizeIdent => $auxDecIdent $freshSizeIdent $freshSizeIdent $outerParams*)



/-- Derives a checker which checks the `inductiveProp` (an inductive relation, represented as a `TSyntax term`)
    using the unification algorithm from Generating Good Generators and the schedules discuseed in Testing Theorems -/
def deriveScheduledChecker (inductiveProp : TSyntax `term) : CommandElabM (TSyntax `command) := do
  -- Parse `inductiveProp` for an application of the inductive relation
  let (inductiveSyntax, argIdents) ← parseInductiveApp inductiveProp
  let inductiveName := inductiveSyntax.getId

  -- Obtain Lean's `InductiveVal` data structure, which contains metadata about the inductive relation
  let inductiveVal ← getConstInfoInduct inductiveName

  -- Determine the type for each argument to the inductive
  let (_, _, inductiveTypeComponents) ← liftTermElabM $ decomposeType inductiveVal.type

  -- To obtain the type of each arg to the inductive,
  -- we pop the last element (`Prop`) from `inductiveTypeComponents`
  let argTypes := inductiveTypeComponents.pop
  let argNames := (fun ident => ident.getId) <$> argIdents
  let argNamesTypes := argNames.zip argTypes

  -- Add the name & type of each argument to the inductive relation to the `LocalContext`
  -- Then, derive `baseProducers` & `inductiveProducers` (the code for the sub-producers
  -- that are invoked when `size = 0` and `size > 0` respectively),
  -- and obtain freshened versions of the output variable / arguments (`freshenedOutputName`, `freshArgIdents`)
  let (baseCheckers, inductiveCheckers, freshArgIdents, localCtx) ←
    liftTermElabM $ withLocalDeclsDND argNamesTypes (fun _ => do
      let mut localCtx ← getLCtx
      let mut freshUnknowns := #[]

      -- For each arg to the inductive relation (as specified to the user),
      -- create a fresh name (to avoid clashing with names that may appear in constructors
      -- of the inductive relation). Note that this requires updating the `LocalContext`.
      for argName in argNames do
        let freshArgName := localCtx.getUnusedName argName
        localCtx := localCtx.renameUserName argName freshArgName
        freshUnknowns := freshUnknowns.push freshArgName

      let mut nonRecursiveCheckers := #[]
      let mut recursiveCheckers := #[]
      let mut requiredInstances := #[]

      for ctorName in inductiveVal.ctors do
        let scheduleOption ← (UnifyM.runInMetaM
          (getCheckerScheduleForInductiveConstructor inductiveName ctorName freshUnknowns.toList)
            emptyUnifyState)
        match scheduleOption with
        | some schedule =>
          -- Obtain a sub-checker for this constructor, along with an array of all typeclass instances that need to be defined beforehand.
          -- (Under the hood, we compile the schedule to an `MExp`, then compile the `MExp` to a Lean term containing the code for the sub-producer.
          -- This is all done in a state monad: when we detect that a new instance is required, we append it to an array of `TSyntax term`s
          -- (where each term represents a typeclass instance)
          let (subChecker, instances) ← StateT.run (s := #[]) (do
            let mexp ← scheduleToMExp schedule (.MId `size) (.MId `initSize)
            mexpToTSyntax mexp (deriveSort := .Checker))

          requiredInstances := requiredInstances ++ instances

          -- Determine whether the constructor is recursive
          -- (i.e. if the constructor has a hypothesis that refers to the inductive relation we are targeting)
          let isRecursive ← isConstructorRecursive inductiveName ctorName

          -- Sub-checkers need to be thunked, since we don't want the `checkerBacktrack` combinator
          -- (which expects a list of sub-checkers as inputs) to evaluate all the sub-checkers eagerly
          let thunkedSubChecker ← `(fun _ => $subChecker)

          if isRecursive then
            recursiveCheckers := recursiveCheckers.push thunkedSubChecker
          else
            nonRecursiveCheckers := nonRecursiveCheckers.push thunkedSubChecker

        | none => throwError m!"Unable to derive producer schedule for constructor {ctorName}"

      if (not requiredInstances.isEmpty) then
        let deduplicatedInstances := List.eraseDups requiredInstances.toList
        logWarning m!"Required typeclass instances (please derive these first if they aren't already defined):\n{deduplicatedInstances}"

      -- Collect all the base / inductive checkers into two Lean list terms
      -- Base checkers are invoked when `size = 0`, inductive checkers are invoked when `size > 0`
      let baseCheckers ← `([$nonRecursiveCheckers,*])
      let inductiveCheckers ← `([$nonRecursiveCheckers,*, $recursiveCheckers,*])

      return (baseCheckers, inductiveCheckers, Lean.mkIdent <$> freshUnknowns, localCtx))

  -- Create an instance of the `DecOpt` typeclass
  mkTopLevelCheckerNEW
    baseCheckers
    inductiveCheckers
    inductiveSyntax
    freshArgIdents
    localCtx

/-- Produces an instance of the `DecOpt` typeclass containing the definition for the top-level derived checker.
    The arguments to this function are:
    - a list of `baseCheckers` (each represented as a Lean term), to be invoked when `size == 0`
    - a list of `inductiveCheckers`, to be invoked when `size > 0`
    - the name of the inductive relation (`inductiveStx`)
    - the arguments (`args`) to the inductive relation -/
def mkTopLevelChecker (baseCheckers : TSyntax `term) (inductiveCheckers : TSyntax `term)
  (inductiveStx : TSyntax `term) (args : TSyntaxArray `term) (topLevelLocalCtx : LocalContext) (nameMap : HashMap Name Name) : CommandElabM (TSyntax `command) := do

  -- Produce a fresh name for the `size` argument for the lambda
  -- at the end of the checker function, as well as the `aux_dec` inner helper function
  let freshSizeIdent := mkFreshAccessibleIdent topLevelLocalCtx `size
  let freshSize' := mkFreshAccessibleIdent topLevelLocalCtx `size'
  let auxDecIdent := mkFreshAccessibleIdent topLevelLocalCtx `aux_dec
  let checkerType ← `($optionTypeConstructor $boolIdent)

  let inductiveName := inductiveStx.raw.getId

  -- Create the cases for the pattern-match on the size argument
  let mut caseExprs := #[]
  let zeroCase ← `(Term.matchAltExpr| | $(mkIdent ``Nat.zero) => $checkerBacktrackFn $baseCheckers)
  caseExprs := caseExprs.push zeroCase

  let succCase ← `(Term.matchAltExpr| | $(mkIdent ``Nat.succ) $freshSize' => $checkerBacktrackFn $inductiveCheckers)
  caseExprs := caseExprs.push succCase

  -- Create function arguments for the checker's `size` & `initSize` parameters
  -- (former is the generator size, latter is the size argument with which to invoke other auxiliary generators/checkers)
  let initSizeParam ← `(Term.letIdBinder| ($initSizeIdent : $natIdent))
  let sizeParam ← `(Term.letIdBinder| ($sizeIdent : $natIdent))
  let matchExpr ← liftTermElabM $ mkMatchExpr sizeIdent caseExprs

  -- Add parameters for each argument to the inductive relation
  let paramInfo ← analyzeInductiveArgs inductiveName args

  -- Inner params are for the inner `aux_dec` function
  let mut innerParams := #[]
  innerParams := innerParams.push initSizeParam
  innerParams := innerParams.push sizeParam

  -- Outer params are for the top-level lambda function which invokes `aux_dec`
  let mut outerParams := #[]
  for (paramName, paramType) in paramInfo do
    let outerParamIdent := mkIdent paramName
    outerParams := outerParams.push outerParamIdent

    -- Each parameter to the inner `aux_arb` function needs to be a fresh name
    -- (so that if we pattern match on the parameter, we avoid pattern variables from shadowing it)
    -- We obtain this fresh name by looking up in the `nameMap`
    let innerParamIdent := lookupFreshenedNameInNameMap nameMap (Array.map Prod.fst paramInfo) paramName

    let innerParam ← `(Term.letIdBinder| ($innerParamIdent : $paramType))
    innerParams := innerParams.push innerParam

  -- Produces an instance of the `DecOpt` typeclass containing the definition for the derived generator
  `(instance : $decOptTypeclass ($inductiveStx $args*) where
      $unqualifiedDecOptFn:ident :=
        let rec $auxDecIdent:ident $innerParams* : $checkerType :=
          $matchExpr
        fun $freshSizeIdent => $auxDecIdent $freshSizeIdent $freshSizeIdent $outerParams*)

/-- Produces an instance of the `DecOpt` typeclass for an inductively-defined proposition type
    represented by `indProp` (Note: the main logic for determining the structure of the derived checker.
    is contained in this function.) -/
def mkDecOptInstance (indProp : TSyntax `term) : CommandElabM (TSyntax `command) := do
  -- Parse the for an application of the inductive relation
  let (inductiveName, args) ← deconstructInductiveApplication indProp

  -- Elaborate the name of the inductive relation and the type
  -- of the value to be generated
  let inductiveExpr ← liftTermElabM $ elabTerm inductiveName none

  let argNameStrings := convertIdentsToStrings args

  -- Create an auxiliary `SubGeneratorInfo` structure that
  -- stores the metadata for each derived sub-generator
  let (allSubCheckerInfos, topLevelLocalCtx, nameMap) ← liftTermElabM $ getSubCheckerInfos inductiveExpr argNameStrings

  -- Every generator is an inductive generator
  -- (they can all be invoked in the inductive case of the top-level generator),
  -- but only certain generators qualify as `BaseGenerator`s
  let baseCheckerInfos := Array.filter (fun checker => checker.checkerSort == .BaseChecker) allSubCheckerInfos
  let inductiveCheckerInfos := allSubCheckerInfos

  let baseCheckers ← liftTermElabM $ mkThunkedSubCheckers baseCheckerInfos
  let inductiveCheckers ← liftTermElabM $ mkThunkedSubCheckers inductiveCheckerInfos

  -- Produce an instance of the `DecOpt` typeclass
  mkTopLevelChecker baseCheckers inductiveCheckers inductiveName args topLevelLocalCtx nameMap

----------------------------------------------------------------------
-- NEW Command elaborator driver
-----------------------------------------------------------------------

/-- Command which derives a checker using the new schedule and unificaiton-based algorithm -/
syntax (name := derive_scheduled_checker) "#derive_scheduled_checker" "(" term ")" : command

/-- Command elaborator that produces the function header for the checker -/
@[command_elab derive_scheduled_checker]
def elabDeriveScheduledChecker : CommandElab := fun stx => do
  match stx with
  | `(#derive_scheduled_checker ( $indProp:term )) => do

    -- Produce an instance of the `DecOpt` typeclass corresponding to the inductive proposition `indProp`
    let typeclassInstance ← deriveScheduledChecker indProp

    -- Pretty-print the derived checker
    let genFormat ← liftCoreM (PrettyPrinter.ppCommand typeclassInstance)

    -- Display the code for the derived checker to the user
    -- & prompt the user to accept it in the VS Code side panel
    liftTermElabM $ Tactic.TryThis.addSuggestion stx
      (Format.pretty genFormat) (header := "Try this checker: ")

    -- Elaborate the typeclass instance and add it to the local context
    elabCommand typeclassInstance

  | _ => throwUnsupportedSyntax

inductive squareOf : Nat → Nat → Prop where
  | sq : forall n, squareOf n (n * n)

-- Dummy EnumSizedSuchThat instance
instance : EnumSizedSuchThat Nat fun m_1 => m_1 = n_1 * n_1 where
  enumSizedST := sorry

/--
info: Try this checker: instance : DecOpt (squareOf n_1 m_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (n_1 : Nat) (m_1 : Nat) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            EnumeratorCombinators.enumeratingOpt
              (EnumSizedSuchThat.enumSizedST (fun m_1 => Eq m_1 (HMul.hMul n_1 n_1)) initSize)
              (fun m_1 => Option.some Bool.true) initSize]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            EnumeratorCombinators.enumeratingOpt
              (EnumSizedSuchThat.enumSizedST (fun m_1 => Eq m_1 (HMul.hMul n_1 n_1)) initSize)
              (fun m_1 => Option.some Bool.true) initSize,
            ]
    fun size => aux_dec size size n_1 m_1
-/
#guard_msgs(info, drop warning) in
#derive_scheduled_checker (squareOf n m)


----------------------------------------------------------------------
-- OLD Command elaborator driver
-----------------------------------------------------------------------

syntax (name := derive_checker) "#derive_checker" "(" term ")" : command

/-- Command elaborator that produces the function header for the checker -/
@[command_elab derive_checker]
def elabDeriveChecker : CommandElab := fun stx => do
  match stx with
  | `(#derive_checker ( $indProp:term )) => do

    -- Produce an instance of the `DecOpt` typeclass corresponding to the inductive proposition `indProp`
    let typeclassInstance ← mkDecOptInstance indProp

    -- Pretty-print the derived checker
    let genFormat ← liftCoreM (PrettyPrinter.ppCommand typeclassInstance)

    -- Display the code for the derived checker to the user
    -- & prompt the user to accept it in the VS Code side panel
    liftTermElabM $ Tactic.TryThis.addSuggestion stx
      (Format.pretty genFormat) (header := "Try this checker: ")

    -- Elaborate the typeclass instance and add it to the local context
    elabCommand typeclassInstance

  | _ => throwUnsupportedSyntax
