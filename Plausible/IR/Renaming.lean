import Lean
import Std
import Plausible.IR.Constructor
import Plausible.IR.GCCall

open Lean Meta Std Plausible.IR

-- Extract pattern variables from a match case expression
def extractPatternVariables (matchCase : Expr) : MetaM (Array FVarId) := do
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
      -- This is a constructor like `Nat.zero`, `List.nil` - no variables to collect
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




-- -- Simplified approach using LocalContext.renameUserName
def renameVariablesInSubGeneratorSimple (subGen : SubGeneratorInfo) : MetaM LocalContext := do
  logInfo m!"=== SIMPLE RENAMING APPROACH ==="

  -- Collect all FVarIds that need renaming
  let mut fvarsToRename : Array FVarId := #[]

  for (scrutineeName, matchCase) in subGen.inputsToMatch.zip subGen.matchCases do
    let patternVars ← extractPatternVariables matchCase
    for patternVar in patternVars do
      let patternVarName ← patternVar.getUserName
      if patternVarName.toString == scrutineeName then
        logInfo m!"Found shadowing: {patternVarName} shadows scrutinee '{scrutineeName}'"
        fvarsToRename := fvarsToRename.push patternVar

  -- Apply renaming using LocalContext.renameUserName
  let mut lctx ← getLCtx

  if fvarsToRename.isEmpty then
    logInfo m!"No shadowing found - returning original"
    return lctx


  for fvar in fvarsToRename do
    let oldName ← fvar.getUserName
    let newName := (LocalContext.getUnusedName lctx oldName)
    logInfo m!"Renaming {oldName} → {newName}"

    lctx := lctx.renameUserName oldName newName

  return lctx



-- Test the simple approach
def testSimpleRenaming : MetaM Unit := do
  withLocalDeclD `n (Expr.const `Nat []) fun nExpr => do
  withLocalDeclD `size' (Expr.const `Nat []) fun sizeExVar => do
  withLocalDeclD `l (Expr.const `Tree []) fun lExpr => do


    logInfo m!"=== TESTING SIMPLE RENAMING ==="
    logInfo m!"Original nExpr name: {nExpr}"

    -- Create a match case that causes shadowing
    let matchCase := Expr.app (Expr.const `Nat.succ []) nExpr
    logInfo m!"Match case: {matchCase}"

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
      variableEqualities := #[]
    }

    logInfo m!"Before renaming - nExpr name: {nExpr}"
    logInfo m!"Before renaming - match case: {matchCase}"
    logInfo m!"Before renaming - aux call: {auxArbCall}"

    -- Apply the simple renaming
    let newLCtx ← renameVariablesInSubGeneratorSimple originalSubGen
    withLCtx' newLCtx do

      logInfo m!"After renaming - nFVar name: {nExpr}"
      logInfo m!"After renaming - match case: {originalSubGen.matchCases[0]!}"

      if let some (Action.genFVar _ renamedAuxCall) := originalSubGen.groupedActions.gen_list[0]? then
        logInfo m!"After renaming - aux call: {renamedAuxCall}"


#eval testSimpleRenaming
