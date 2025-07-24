import Lean
import Plausible.IR.Examples
import Plausible.New.Utils
import Plausible.GeneratingGoodGenerators.UnificationMonad
import Plausible.GeneratingGoodGenerators.DeriveSubGenerator

open Lean Meta
open Plausible.IR

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

/-- A `HypothesisExpr` is a datatype representing a hypothesis for a
    constructor of an inductive relation, consisting of a constructor name
    applied to some list of arguments, each of which are `ConstructorExpr`s -/
abbrev HypothesisExpr := Name × List ConstructorExpr

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

-- def collectCheckSteps (boundVars : List Name) (checkedHypotheses : List Nat) (sortedHypotheses : )


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
