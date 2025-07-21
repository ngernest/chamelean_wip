import Plausible.IR.Examples
import Plausible.New.OptionTGen
import Plausible.New.ArbitrarySizedSuchThat
import Plausible.New.DecOpt
import Plausible.New.OptionTGenTheorems
import Lean
import Plausible.Gen
open Plausible
open OptionTGen

open ArbitrarySizedSuchThat
open Lean Elab Tactic Meta PrettyPrinter

/-
def genBST (lo : Nat) (hi : Nat) : Nat → OptionT Gen Tree :=
  let rec aux_arb (initSize : Nat) (size : Nat) (lo_0 : Nat) (hi_0 : Nat) : OptionT Gen Tree :=
    match size with
    | .zero =>
      backtrack [
        (1, thunkGen $ fun _ => pure .Leaf),
        (1, thunkGen $ fun _ => OptionT.fail)
      ]
    | .succ size' =>
      backtrack [
        (1, thunkGen $ fun _ => pure .Leaf),
        (.succ size', thunkGen $ fun _ => do
          let x ← SampleableExt.interpSample Nat
          if (lo_0 < x && x < hi_0) then
            let l ← aux_arb initSize size' lo_0 x
            let r ← aux_arb initSize size' x hi_0
            pure (.Node x l r)
          else OptionT.fail)
      ]
    termination_by size
  fun size => aux_arb size size lo hi

theorem genBST_correct {size: Nat}: OptionTGenEnsure (bst lo hi) (genBST lo hi size) := by
  unfold genBST
  generalize h: size = initsize
  symm at h
  rw (occs:=.pos [2]) [h]
  clear h
  induction size generalizing lo hi
  simp only [genBST.aux_arb, thunkGen]
  apply OptionTGenEnsure_backtrack
  simp only [OptionTGenListEnsure, List.unzip_cons, List.unzip_nil, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq]
  constructor <;>  try exact OptionTGenEnsure_of_fail
  rw[OptionTGenEnsure_pure]
  apply bst.BstLeaf
  rename_i size ind
  simp [genBST.aux_arb, thunkGen]
  apply OptionTGenEnsure_backtrack
  simp [OptionTGenListEnsure]
  constructor
  rw[OptionTGenEnsure_pure]
  apply bst.BstLeaf
  apply OptionTGenEnsure_bind_forall; intro b
  split <;> try exact OptionTGenEnsure_of_fail
  have ind1:= @ind lo b
  have ind2:= @ind b hi
  apply OptionTGenEnsure_bind (bst lo b) (bst lo hi) ind1;
  intro b1 hb1
  apply OptionTGenEnsure_bind (bst b hi) (bst lo hi) ind2;
  intro b2 hb2
  rw [OptionTGenEnsure_pure]
  rename_i hc; cases hc
  apply bst.BstNode;
  any_goals assumption;
-/

elab "splitands" : tactic  => withMainContext do
  let goal ← getMainGoal
  let goalType ← goal.getType
  let goalDecl ← goal.getDecl
  let rec collectAnds (e : Expr) : TacticM (List Expr) := do
    match e with
    | Expr.app (Expr.app (Expr.const `And _) left) right =>
      let rightGoals ← collectAnds right
      return left::rightGoals
    | _ => return [e]
  let subgoals ← collectAnds goalType
  if subgoals.length ≤ 1 then
    throwError "Goal is not a conjunction"
  let mut goalsarray := #[]
  for s in subgoals do
    let newmvar ← mkFreshExprMVarAt goalDecl.lctx goalDecl.localInstances s
    goalsarray := goalsarray.push newmvar
  let goals:= goalsarray.toList.map Expr.mvarId!
  let rec reconstructand (es: List Expr) : MetaM Expr := do
    match es with
    | h::t => match t with | [] => return h | _ => mkAppM `And.intro #[h, ← reconstructand t]
    | [] => return (Expr.const `True [])
  goal.assign (← reconstructand goalsarray.toList)
  setGoals (goals ++ (← getGoals).drop 1)


def getCtorName (inputExpr : Expr)  : MetaM (Array Name) := do
  match inputExpr.getAppFn.constName? with
  | some inductive_name => do
    let env ← getEnv
    match env.find? inductive_name with
    | none => throwError "Type '{inductive_name}' not found"
    | some (ConstantInfo.inductInfo info) => do
      let mut ctors : Array Name := #[]
      for ctorName in info.ctors do
        ctors:= ctors.push ctorName
      return ctors
    | some _ =>
      throwError "'{inductive_name}' is not an inductive type"
  | none => throwError "Not a type"

def withRollback (tac : TacticM Unit) : TacticM Unit := do
  let state ← saveState
  try
    tac
  catch _ =>
    restoreState state

def non_rec_proof (x: Name) : TacticM Unit := do
  let goal ← getMainTarget
  let appfn := goal.getAppArgs[2]!
  let appfnname:= appfn.getAppFn.constName
  evalTactic (← `(tactic| try split))
  if appfnname = `Pure.pure then
    evalTactic (← `(tactic| rw[OptionTGenEnsure_pure]))
    evalTactic (← `(tactic| apply $(mkIdent x)))
  else if appfnname = `OptionT.fail then
    evalTactic (← `(tactic| exact OptionTGenEnsure_of_fail))
  else
    evalTactic (← `(tactic| unfold OptionTGenEnsure))
    evalTactic (← `(tactic| rw[← OptionTGenEnsure]))
    evalTactic (← `(tactic| rw[OptionTGenEnsure_pure]))
    evalTactic (← `(tactic| try simp_all [DecOpt.decOpt]))
    evalTactic (← `(tactic| apply $(mkIdent x)))
    evalTactic (← `(tactic| exact OptionTGenEnsure_of_fail))

def try_non_rec_proof (x: Name) : TacticM Unit := withRollback (non_rec_proof x)

def replace_unbound_args (e: Expr) (a: Array Expr) : MetaM Expr := do
  match e with
  | Expr.lam x b body b1 =>
    let mut newargs := #[]
    let mut aindex := 0
    for arg1 in body.getAppArgs do
      if arg1.isBVar then
        newargs:= newargs.push arg1
      else
        newargs:= newargs.push a[aindex]!
        aindex := aindex + 1
    let newbody := mkAppN (body.getAppFn) newargs
    return Expr.lam x b newbody b1
  | _ => return mkAppN (e.getAppFn) a

def unfold_bind (recfunname: Name) (ircond: Expr): TacticM Unit := withMainContext do
  let goal ← getMainTarget
  let appfn := goal.getAppArgs[2]!
  let args := appfn.getAppArgs
  let bind1:= args[args.size-2]!
  let bind1fn := bind1.getAppFn.constName
  if bind1fn = `liftM then
    evalTactic (← `(tactic| apply OptionTGenEnsure_bind_forall))
    evalTactic (← `(tactic| intros))
    let new_goal ← getMainTarget
    let currentfn := new_goal.getAppArgs[2]!.getAppFn.constName
    if currentfn = `ite then
      evalTactic (← `(tactic| split <;> try exact OptionTGenEnsure_of_fail))
      evalTactic (← `(tactic| rename_i hctemp ))
      evalTactic (← `(tactic| cases hctemp ))
  else if bind1fn = recfunname then
    let pn ← replace_unbound_args ircond (bind1.getAppArgs.drop 2)
    let pnterm ← PrettyPrinter.delab pn
    let ircondterm ← PrettyPrinter.delab ircond
    let ind := mkIdent `ind
    evalTactic (← `(tactic| apply OptionTGenEnsure_bind $pnterm:term $ircondterm:term ))
    evalTactic (← `(tactic| apply $ind ))
    evalTactic (← `(tactic| intros ))
  else
    throwError "bind1 {bind1fn} is not supported {recfunname} with {← Meta.ppExpr ircond}"


def rec_proof (x: Name) (y: Name): TacticM Unit := do
  evalTactic (← `(tactic| try split))
  evalTactic (← `(tactic| any_goals try exact OptionTGenEnsure_of_fail))
  let goal ← getMainTarget
  let ircond := goal.getAppArgs[1]!
  let appfn := goal.getAppArgs[2]!
  let appfnname:= appfn.getAppFn.constName
  if appfnname = `Pure.pure then
    evalTactic (← `(tactic| rw[OptionTGenEnsure_pure]))
    evalTactic (← `(tactic| apply $(mkIdent x)))
  else if appfnname = `OptionT.fail then
    evalTactic (← `(tactic| exact OptionTGenEnsure_of_fail))
  else if appfnname = `Bind.bind then
    let mut currentfn := appfnname
    while currentfn = `Bind.bind do
      unfold_bind y ircond
      let new_goal ← getMainTarget
      currentfn := new_goal.getAppArgs[2]!.getAppFn.constName
    evalTactic (← `(tactic| rw[OptionTGenEnsure_pure]))
    evalTactic (← `(tactic| apply $(mkIdent x)))
    evalTactic (← `(tactic| any_goals assumption))
  else
    throwError "Goal {appfnname} is not supported"

def try_rec_proof (x: Name) (y: Name): TacticM Unit := withRollback (rec_proof x y)

def get_IR (e: Expr) : Expr :=
  match e with
  | Expr.app _ _ => e.getAppFn
  | Expr.lam _ _ body _ => body.getAppFn
  | _ => e.getAppFn

elab "gen_proof" : tactic => withMainContext do
  let goal ← getMainTarget
  let ircond := goal.getAppArgs[1]!
  let ir := get_IR ircond
  let size := mkIdent `size
  let ind := mkIdent `ind
  let initsize := mkIdent `initsize
  let initsize_eq_size := mkIdent `initsize_eq_size
  let ctors ←  getCtorName ir
  let appfnname := goal.getAppFn.constName
  if appfnname = `OptionTGenEnsure then
    let genexpr:= goal.getAppArgs[2]!
    let gen_fn := mkIdent (  genexpr.getAppFn.constName)
    evalTactic (← `(tactic| unfold $gen_fn))
    evalTactic (← `(tactic| generalize $initsize_eq_size:ident : $size:ident = $initsize:ident))
    evalTactic (← `(tactic| symm at  $initsize_eq_size:ident ))
    evalTactic (← `(tactic| rw (occs:=.pos [2]) [ $initsize_eq_size:ident ]))
    evalTactic (← `(tactic| clear $initsize_eq_size:ident))
    let curgoal ← getMainTarget
    let curgenexpr:= curgoal.getAppArgs[2]!
    --dbg_trace "Args: {curgenexpr.getAppArgs.toList.drop 2}"
    let argsname  := ((curgenexpr.getAppArgs.toList.drop 2).map Lean.Expr.fvarId!).mapM FVarId.getUserName
    let args:= ((← argsname).map Lean.mkIdent).toArray
    evalTactic (← `(tactic| induction $size:ident generalizing $(args)*))
    let aux_fn := mkIdent (  curgenexpr.getAppFn.constName)
    evalTactic (← `(tactic| unfold $aux_fn))
    evalTactic (← `(tactic| simp only [thunkGen]))
    evalTactic (← `(tactic| apply OptionTGenEnsure_backtrack))
    evalTactic (← `(tactic| simp only [OptionTGenListEnsure, List.unzip_cons, List.unzip_nil, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq]))
    evalTactic (← `(tactic| try splitands))
    for ctor in ctors do
      try_non_rec_proof ctor
    evalTactic (← `(tactic| try exact OptionTGenEnsure_of_fail))
    evalTactic (← `(tactic| rename_i $size:ident $ind:ident))
    evalTactic (← `(tactic| unfold $aux_fn))
    evalTactic (← `(tactic| simp only [thunkGen]))
    evalTactic (← `(tactic| apply OptionTGenEnsure_backtrack))
    evalTactic (← `(tactic| simp [OptionTGenListEnsure]))
    evalTactic (← `(tactic| try splitands))
    for ctor in ctors do
      try_non_rec_proof ctor
    if (← getGoals).isEmpty then
      return
    for ctor in ctors do
      try_rec_proof ctor curgenexpr.getAppFn.constName
  else
    throwError "Goal {appfnname} is not supported"


/-
theorem genBST_correct: OptionTGenEnsure (bst lo hi) (genBST lo hi size) := by
  gen_proof

/-
info: Try this generator: instance : ArbitrarySizedSuchThat Nat (fun x => lookup Γ x τ) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (Γ_0 : List type) (τ_0 : type) : OptionT Plausible.Gen Nat :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              OptionTGen.thunkGen
                (fun _ =>
                  match Γ_0 with
                  | τ :: Γ =>
                    match DecOpt.decOpt (τ = τ_0) initSize with
                    | Option.some Bool.true => pure 0
                    | _ => OptionT.fail
                  | _ => OptionT.fail)),
            (1, OptionTGen.thunkGen (fun _ => OptionT.fail))]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              OptionTGen.thunkGen
                (fun _ =>
                  match Γ_0 with
                  | τ :: Γ =>
                    match DecOpt.decOpt (τ = τ_0) initSize with
                    | Option.some Bool.true => pure 0
                    | _ => OptionT.fail
                  | _ => OptionT.fail)),
            (Nat.succ size',
              OptionTGen.thunkGen
                (fun _ =>
                  match Γ_0 with
                  | τ' :: Γ => do
                    let n ← aux_arb initSize size' Γ τ
                    return Nat.succ n
                  | _ => OptionT.fail))]
    fun size => aux_arb size size Γ τ
-/
-/
