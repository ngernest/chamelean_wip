
import Lean
import Plausible.IR.Prelude
import Batteries.Data.List.Basic

open Lean Meta LocalContext Std
open Plausible.IR

/-- Monad instance for List.
    Note that:
    - The Lean standard library does not have a Monad instance for List (see https://leanprover-community.github.io/archive/stream/270676-lean4/topic/Option.20do.20notation.20regression.3F.html#231433226)
    - MathLib4 does have a Monad instance for List, but we wish to avoid having Chamelean rely on Mathlib
    as a dependency, so we reproduce the Monad instance for Lists here instead. -/
instance : Monad List where
  pure x := [x]
  bind xs f := xs.flatMap f

/-- Decomposes an list `xs` into a pair `(xs', x)`
   where `xs' = xs[0..=n-2]` and `x = xs[n - 1]` (where `n` is the length of `xs`).
   - If `xs` is empty, this function returns `none`
   - If `xs = #[x]`, this function returns `some (#[], x)`
   - Note: this function is the same as `unsnoc` in Haskell's `Data.List` library -/
def unsnoc (xs : List α) : Option (List α × α) :=
  match xs.getLast? with
  | none => none
  | some x => some (xs.take (xs.length - 1), x)

/-- Variant of `List.flatMap` where the function `f` expects two arguments:
    the current argument of the list and all *other* elements in the list (in order) excluding the current one.
    Intuitively, this is a version of `flatMap` where each element is processed
    by `f` with contextual information from the other elements. -/
def flatMapWithContext (xs : List α) (f : α → List α → List β) : List β :=
  aux [] xs
    where
      aux (acc : List α) (l : List α) : List β :=
        match l with
        | [] => []
        | hd :: tl => f hd (List.reverse acc ++ tl) ++ aux (hd :: acc) tl

/-- Variant of `flatMapWithContext` where the function `f` is monadic
    and returns `m (List β)` -/
def flatMapMWithContext [Monad m] (xs : List α) (f : α → List α → m (List β)) : m (List β) :=
  aux [] xs
    where
      aux (acc : List α) (l : List α) : m (List β) :=
        match l with
        | [] => return []
        | hd :: tl => do
            let xs ← f hd (List.reverse acc ++ tl)
            let ys ← aux (hd :: acc) tl
            return (xs ++ ys)


/-- Variant of `List.filterMap` where the function `f` also takes in the index of the
    current element in the list -/
def filterMapWithIndex (f : Nat → α → Option β) (xs : List α) : List β :=
  xs.zipIdx.filterMap (Function.uncurry $ flip f)

/-- Variant of `List.filterMapM` where the function `f` also takes in the index of the
    current element in the list -/
def filterMapMWithIndex [Monad m] (f : Nat → α → m (Option β)) (xs : List α) : m (List β) :=
  xs.zipIdx.filterMapM (Function.uncurry $ flip f)

/-- `mkInitialContextForInductiveRelation inputTypes inputNames`
    creates the initial `LocalContext` where each `(x, τ)` in `Array.zip inputTypes inputNames`
    is given the declaration `x : τ` in the resultant context.

    This function returns a quadruple containing `inputTypes`, `inputNames` represented as an `Array` of `Name`s,
    the resultant `LocalContext` and a map from original names to freshened names. -/
def mkInitialContextForInductiveRelation (inputTypes : Array Expr) (inputNames : Array Name) : MetaM (Array Expr × Array Name × LocalContext × HashMap Name Name) := do
  let localDecls := inputNames.zip inputTypes
  withLocalDeclsDND localDecls $ fun exprs => do
    let mut nameMapBindings := #[]
    let mut localCtx ← getLCtx
    for currentName in inputNames do
      let freshName := getUnusedName localCtx currentName
      localCtx := renameUserName localCtx currentName freshName
      nameMapBindings := nameMapBindings.push (currentName, freshName)
    let nameMap := HashMap.ofList (Array.toList nameMapBindings)
    return (exprs, inputNames, localCtx, nameMap)


/-- Looks up the user-facing `Name` corresponding to an `FVarId` in a specific `LocalContext`
    - Panics if `fvarId` is not in the `LocalContext` -/
def getUserNameInContext! (lctx : LocalContext) (fvarId : FVarId) : Name :=
  (lctx.get! fvarId).userName

/-- Helper function for setting delaborator options
  (used in `delabExprInLocalContext`, which calls `PrettyPrinter.delab`)

  - Note: this function forces delaborator to pretty-print pattern cases in prefix position,
    as opposed to using postfix dot-notation, which is not allowed in pattern-matches -/
def setDelaboratorOptions (opts : Options) : Options :=
  opts.setBool `pp.fieldNotation false
    |>.setBool `pp.notation true
    |>.setBool `pp.instances true
    |>.setBool `pp.instanceTypes false
    |>.setBool `pp.all false
    |>.setBool `pp.explicit false


/-- Delaborates an `Expr` in a `LocalContext` to a `TSyntax term` -/
def delabExprInLocalContext (lctx : LocalContext) (e : Expr) : MetaM (TSyntax `term) :=
  withOptions setDelaboratorOptions $
    withLCtx lctx #[] do
      PrettyPrinter.delab e

/-- Determines if an instance of the typeclass `className` exists for a particular `type`
    represented as an `Expr`. Under the hood, this tries to synthesize an instance of the typeclass for the type.

    Example:
    ```
    #eval hasInstance `Repr (Expr.const `Nat []) -- returns true
    ```
-/
def hasInstance (className : Name) (type : Expr) : MetaM Bool := do
  let classType ← mkAppM className #[type]
  Option.isSome <$> synthInstance? classType


/-- Determines if a constructor for an inductive relation is *recursive*
    (i.e. the constructor's type mentions the inductive relation)
    - Note: this function only considers constructors with arrow types -/
def isConstructorRecursive (inductiveName : Name) (ctorName : Name) : MetaM Bool := do
  let ctorInfo ← getConstInfo ctorName
  let ctorType := ctorInfo.type

  let (_, _, type_exprs_in_arrow_type) ← decomposeType ctorType
  match splitLast? type_exprs_in_arrow_type with
  | some (hypotheses, _conclusion) =>
    for hyp in hypotheses do
      if hyp.getAppFn.constName == inductiveName then
        return true
    return false
  | none => throwError "constructors with non-arrow types are not-considered to be recursive"

/-- `replicateM n act` performs the action `act` for `n` times, returning a list of results. -/
def replicateM [Monad m] (n : Nat) (action : m α) : m (List α) :=
  match n with
  | 0 => pure []
  | n + 1 => do
    let x ← action
    let xs ← replicateM n action
    pure (x :: xs)

/-- Converts a list of options to an optional list
    (akin to Haskell's `sequence`) -/
def List.sequence (xs : List (Option α)) : Option (List α) :=
  List.traverse id xs
