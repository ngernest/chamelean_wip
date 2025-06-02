import Lean
open Lean Elab Command Meta Term Parser

/-- Extracts the name of the induction relation and its arguments (if supplied) -/
def parseInductiveApp (stx : Term) : CommandElabM (Name × Array Term) := do
  match stx with
  | `($f:ident $args:term*) =>
    let name := f.getId
    pure (name, args)
  | `($f:ident) =>
    let name := f.getId
    pure (name, #[])
  | _ => throwErrorAt stx "Expected inductive type application"

/-- Uses the name of the inductive relation to produce the checker's name -/
def makeCheckerName (inductiveName : Name) : Name :=
  Name.mkStr1 s!"check_{inductiveName}"

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

-------------------------------------------------------
-- Command elaborator infrastructure below
-------------------------------------------------------

syntax (name := mk_checker_header) "#mk_checker_header " term : command

/-- Command elaborator that produces the function header for the checker -/
@[command_elab mk_checker_header]
def elabMkCheckerHeader : CommandElab := fun stx => do
  match stx with
  | `(#mk_checker_header ( $inductiveApp:term )) =>
    logInfo s!"Collected: {inductiveApp}"

    -- Parse the names of inductive relation + its arguments
    let (inductiveName, args) ← parseInductiveApp inductiveApp

    if !(← isInductive inductiveName) then
      throwErrorAt stx "{inductiveName} is not an inductive, expected an inductive relation"

    -- Associate each argument with an appropriate type expression
    let paramInfo ← analyzeInductiveArgs inductiveName args

    -- Compute the name for the checker function
    let checkerName := makeCheckerName inductiveName
    let checkerIdent := mkIdent checkerName

    -- Extract parameter names and types from the arguments
    let mut params := #[]

    -- Produce size arguments for the checker
    let sizeParam ← `(bracketedBinder| (size : Nat))
    let topSizeParam ← `(bracketedBinder| (top_size : Nat))
    params := params.push sizeParam
    params := params.push topSizeParam

    -- Process each argument from the inductive application
    for (paramName, paramType) in paramInfo do
      let paramIdent := mkIdent paramName
      let param ← `(bracketedBinder| ($paramIdent : $paramType))
      params := params.push param

    let funHeader : TSyntax `command ←
      `(def $checkerIdent $params* : Option Bool := none)

    let headerFormat ← liftCoreM (PrettyPrinter.ppCommand funHeader)
    logInfo m!"Generated function header:\n{headerFormat}"

    elabCommand funHeader

  | _ => throwUnsupportedSyntax

-----------
-- Testing
-----------

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

#mk_checker_header (typing Γ e τ)
