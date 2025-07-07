import Lean
import Std
import Plausible.IR.Constructor
import Plausible.IR.GCCall

open Lean Meta Std Plausible.IR

/-- Extracts pattern variables from an expression `matchCase` that is a case
    in a pattern-match, returning an array of `FVarId`s -/
def extractPatternVariables (matchCase : Expr) : MetaM (Array FVarId) := do
  -- `collectVars` collects the pattern variables in an `expr`,
  -- with `acc` being the `Array` of `FVarId`s
  -- collected so far, returning an updated `Array` of `FVarId`s
  let rec collectVars (e : Expr) (acc : Array FVarId) : MetaM (Array FVarId) := do
    match e with
    | Expr.fvar id =>
      -- This is a pattern variable (like `n'` in `Nat.succ n'`)
      pure (acc.push id)

    | Expr.app fn arg =>
      -- Handle constructor applications like `Nat.succ n'` or `x :: xs`
      -- The function part (fn) is the constructor, arguments may contain pattern variables

      -- Also check the function in case it's a complex pattern
      let acc' ← collectVars arg acc
      collectVars fn acc'

    | Expr.const _ _ =>
      -- This is a constructor like `Nat.zero` or `List.nil`, so there are
      -- no variables to collect
      pure acc

    | Expr.lam _binderName binderType body _ =>
      -- Lambda in pattern (rare, but handle it)
      let acc' ← collectVars binderType acc
      collectVars body acc'

    | Expr.forallE _binderName binderType body _binderInfo =>
      -- Foralls in pattern (rarely occur)
      let acc' ← collectVars binderType acc
      collectVars body acc'

    | Expr.letE _declName type value body _nonDep =>
      -- Let expression in pattern
      let acc1 ← collectVars type acc
      let acc2 ← collectVars value acc1
      collectVars body acc2

    | Expr.mdata _ expr =>
      -- Skip metadata, recurse on inner expression
      collectVars expr acc

    | Expr.proj _typeName _idx struct =>
      -- Projection pattern (like accessing fields)
      collectVars struct acc

    | Expr.bvar _ =>
      -- Bound variable - shouldn't appear in patterns at this level
      pure acc

    | Expr.mvar _ =>
      -- Metavariable - shouldn't appear in elaborated patterns
      pure acc

    | Expr.sort _ =>
      -- Sort - no variables
      pure acc

    | Expr.lit _ =>
      -- Literal - no variables
      pure acc


  collectVars matchCase #[]

/-- Collects the `FVarId`s corresponding to all pattern variables (variables on the LHS of a pattern match)
    that need renaming. A pattern variable needs to be renamed if it shadows the scrutinee of the pattern match.  -/
def getPatternVarsThatNeedRenaming (subGen : SubGeneratorInfo) : MetaM (Array FVarId) := do
  let mut fvarsToRename : Array FVarId := #[]
  for (scrutineeName, matchCase) in Array.zip subGen.inputsToMatch subGen.matchCases do
    let patternVars ← extractPatternVariables matchCase
    for patternVar in patternVars do
      let patternVarName ← patternVar.getUserName
      -- If the pattern variable's name is the same as the scrutinee's, then shadowing has occurred,
      -- so we need to rename the pattern variable
      if patternVarName.toString == scrutineeName then
        fvarsToRename := fvarsToRename.push patternVar
  pure fvarsToRename


-- -- Simplified approach using LocalContext.renameUserName
def renameVariablesInSubGeneratorSimple (subGen : SubGeneratorInfo) : MetaM LocalContext := do
  let fvarsToRename ← getPatternVarsThatNeedRenaming subGen
  let mut lctx ← getLCtx

  -- No pattern variables shadow the scrutinee, so we can just return the original `LocalContext`
  if fvarsToRename.isEmpty then
    return lctx

  for fvar in fvarsToRename do
    let oldName ← fvar.getUserName
    -- Create a new, user-accessible fresh name using the `LocalContext`
    let newName := LocalContext.getUnusedName lctx oldName

    -- REplace all occurences of the `oldName` in the `LocalContext` with the  `newName`
    lctx := lctx.renameUserName oldName newName

  -- Return updated local context
  -- (callers should use `withLCtx'` to enter the updated local context)
  return lctx


-- Test the simple approach
def testSimpleRenaming : MetaM Unit := do
  withLocalDeclD `n (Expr.const `Nat []) fun nExpr => do
  withLocalDeclD `size' (Expr.const `Nat []) fun sizeExVar => do
  withLocalDeclD `l (Expr.const `Tree []) fun lExpr => do

    -- Create a match case that causes shadowing
    let matchCase := Expr.app (Expr.const `Nat.succ []) nExpr

    -- Create expressions that reference the pattern variable
    let auxArbCall := mkApp2 (Expr.const `aux_arb []) sizeExVar nExpr

    let originalSubGen : SubGeneratorInfo := {
      inputs := #["n"],
      inputsToMatch := #["n"],  -- This should trigger renaming
      matchCases := #[matchCase],
      groupedActions := {
        gen_list := #[Action.genFVar (lExpr.fvarId!) auxArbCall],
        iflet_list := #[],
        checkInductiveActions := #[],
        checkNonInductiveActions := #[],
        ret_list := #[Action.ret (Expr.const `Tree.leaf [])],
        variableEqualities := #[]
      },
      generatorSort := .InductiveGenerator,
      variableEqualities := #[],
      producerType := .Generator
    }

    logWarning m!"Before renaming - nExpr name: {nExpr}"
    logWarning m!"Before renaming - match case: {matchCase}"
    logWarning m!"Before renaming - aux call: {auxArbCall}"

    -- Apply the simple renaming
    let newLCtx ← renameVariablesInSubGeneratorSimple originalSubGen
    withLCtx' newLCtx do

      logWarning m!"After renaming - nFVar name: {nExpr}"
      logWarning m!"After renaming - match case: {originalSubGen.matchCases[0]!}"

      if let some (Action.genFVar _ renamedAuxCall) := originalSubGen.groupedActions.gen_list[0]? then
        logWarning m!"After renaming - aux call: {renamedAuxCall}"


-- #eval testSimpleRenaming
