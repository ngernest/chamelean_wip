import Lean
import Plausible.Gen

open Lean Elab Command Meta Term Parser
open Plausible.Gen

/-- Extracts the name of the induction relation and its arguments -/
def parseInductiveApp (body : Term) : CommandElabM (Name × TSyntaxArray `term) := do
  match body with
  | `($indRel:ident $args:term*) => do
    return (indRel.getId, args)
  | `($indRel:ident) => do
    return (indRel.getId, #[])
  | _ => throwErrorAt body "Expected inductive type application"

/-- Extracts the name of a parameter from a corresponding `Term`.
    If this is not possible, a fresh user-facing name is produced. -/
def extractParamName (arg : Term) : MetaM Name :=
  match arg with
  | `($name:ident) => pure name.getId
  | _ => Core.mkFreshUserName `param

/-- Analyzes the type of the inductive relation and matches each
    argument with its expected type, returning an array of
    (parameter name, type expression) pairs -/
def analyzeInductiveArgs (inductiveName : Name) (args : Array Term) :
  CommandElabM (Array (Name × TSyntax `term)) := do

  -- Extract the no. of parameters & indices for the inductive
  let inductInfo ← getConstInfoInduct inductiveName
  let numParams := inductInfo.numParams
  let numIndices := inductInfo.numIndices
  let numArgs := numParams + numIndices

  if args.size != numArgs then
    throwError s!"Expected {numArgs} arguments but received {args.size} arguments instead"

  -- Extract the type of the inductive relation
  let inductType := inductInfo.type

  liftTermElabM $
    forallTelescope inductType (fun xs _ => do
      let mut paramInfo : Array (Name × TSyntax `term) := #[]

      for i in [:args.size] do
        -- Match each argument with its expected type
        let arg := args[i]!
        let paramFVar := xs[i]!
        let paramType ← inferType paramFVar

        -- Extract parameter name from the argument syntax
        let paramName ← extractParamName arg

        -- Use Lean's delaborator to express the parameter type
        -- using concrete surface-level syntax
        let typeSyntax ← PrettyPrinter.delab paramType

        paramInfo := paramInfo.push (paramName, typeSyntax)

      pure paramInfo)

/-- Produces the actual generator function.
    - `inductiveName` is the name of the inductive relation
    - `targetVar`, `targetType`: the variable name and type of the value to be generated
    - `args`: the other arguments to the inductive relation -/
def mkGeneratorFunction (inductiveName : Name) (targetVar : Name) (targetType : TSyntax `term)
  (args : TSyntaxArray `term) : CommandElabM (TSyntax `command) := do
  -- Extract the names of the constructors for the inductive
  let inductInfo ← getConstInfoInduct inductiveName
  let constructorNames := inductInfo.ctors

  -- Generate the generator function name
  let genFunName := mkIdent (Name.mkStr1 s!"gen_{inductiveName}")

  -- Build parameter list from the predicate arguments (excluding the target variable)
  -- Add a size parameter for controlling generation depth
  let mut params := #[]
  let sizeParam ← `(bracketedBinder| (size : Nat))
  params := params.push sizeParam

  -- Add parameters for each argument in the predicate (except the target)
  let paramInfo ← analyzeInductiveArgs inductiveName args
  for (paramName, paramType) in paramInfo do
    if paramName != targetVar then
      let paramIdent := mkIdent paramName
      let param ← `(bracketedBinder| ($paramIdent : $paramType))
      params := params.push param

  -- Generate the complete function
  `(def $genFunName $params* : Plausible.Gen $targetType := sorry)

----------------------------------------------------------------------
-- Command elaborator for producing the Plausible generator
-----------------------------------------------------------------------

syntax (name := derive_generator) "#derive_generator" "(" "fun" "(" ident ":" term ")" "=>" term ")" : command

@[command_elab derive_generator]
def elabDeriveGenerator : CommandElab := fun stx => do
  match stx with
  | `(#derive_generator ( fun ( $var:ident : $targetType:term ) => $body:term )) => do
    -- Parse the body of the lambda for an application of the inductive relation
    let (inductiveName, args) ← parseInductiveApp body
    let targetVar := var.getId

    -- `genFunction` is the syntax for the derived generator function
    let genFunction ← mkGeneratorFunction inductiveName targetVar targetType args

    -- Pretty-print the derived generator
    let genFormat ← liftCoreM (PrettyPrinter.ppCommand genFunction)
    logInfo m!"Generated generator function:\n{genFormat}"

    elabCommand genFunction

  | _ => throwUnsupportedSyntax

-----------
-- Testing
-----------

/-- Binary trees containing a `Nat` at each node -/
inductive Tree where
  | Leaf : Tree
  | Node : Nat → Tree → Tree → Tree
  deriving Repr

/-- `bst lo hi t` describes whether a tree `t` is a BST that contains values strictly within `lo` and `hi` -/
inductive bst : Nat → Nat → Tree → Prop where
  | BstLeaf: ∀ lo hi,
      bst lo hi .Leaf
  | BstNode: ∀ lo hi x l r,
      lo < x → x < hi →
      bst lo x l → bst x hi r →
      bst lo hi (.Node x l r)

/-- Base types in the STLC (either Nat or functions) -/
inductive type where
  | Nat : type
  | Arr : type → type → type
  deriving BEq, Repr

/-- Terms in the STLC w/ naturals, where variables are represented using De Bruijn indices -/
inductive term where
  | Const : Nat → term
  | Add : term → term → term
  | Var : Nat → term
  | App : term → term → term
  | Abs : type → term → term
  deriving BEq, Repr

/- `typing Γ e τ` is the typing judgement `Γ ⊢ e : τ`.
    For simplicity, we only include `TConst` and `TAdd` for now (the other cases require auxiliary `inductive`s) -/
inductive typing (Γ : List type) : term → type → Prop where
  | TConst : ∀ n, typing Γ (.Const n) type.Nat
  | TAdd: ∀ e1 e2, typing Γ e1 .Nat → typing Γ e2 .Nat → typing Γ (term.Add e1 e2) .Nat

-- Example usage:
-- (Note: we require users to explicitly provide a type annotation to the argument to the lambda)

-- #derive_generator (fun (t : Tree) => bst lo hi t)
#derive_generator (fun (e : term) => typing Γ e τ)
