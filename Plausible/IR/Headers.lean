import Lean
open Lean Elab Command Meta Term Parser

/-- Extracts the name of the induction relation and its arguments (if supplied) -/
def parseInductiveApp (stx : Term) : CommandElabM (Name × Array Term) := do
  match stx with
  | `($f:ident $args:term*) =>
    let name := f.getId
    return (name, args)
  | `($f:ident) =>
    let name := f.getId
    return (name, #[])
  | _ => throwErrorAt stx "Expected inductive type application"

/-- Uses the name of the inductive relation to produce the checker's name -/
def makeCheckerName (inductiveName : Name) : Name :=
  Name.mkStr1 s!"check_{inductiveName}"

syntax (name := mk_checker_header) "#mk_checker_header " term : command

/-- Command elaborator that produces the function header for the checker -/
@[command_elab mk_checker_header]
def elabMkCheckerHeader : CommandElab := fun stx => do
  match stx with
  | `(#mk_checker_header ( $inductiveApp:term )) =>
    logInfo s!"Collected: {inductiveApp}"

    -- Parse the inductive application
    let (inductiveName, args) ← parseInductiveApp inductiveApp

    if !(← isInductive inductiveName) then
      throwErrorAt stx "{inductiveName} is not an inductive, expected an inductive relation"

    logInfo s!"inductiveName = {inductiveName}, args = {args}"

    -- Generate the checker function name
    let checkerName := makeCheckerName inductiveName
    let checkerIdent := mkIdent checkerName

    -- Extract parameter names and types from the arguments
    -- We'll create parameters for each argument in the inductive application
    let mut params := #[]

    -- Add the standard size parameters
    let sizeParam ← `(bracketedBinder| (size : Nat))
    let topSizeParam ← `(bracketedBinder| (top_size : Nat))
    params := params.push sizeParam
    params := params.push topSizeParam

    -- Process each argument from the inductive application
    for i in [:args.size] do
      let arg := args[i]!

      -- TODO: generalize this to handle any any argument types
      match i with
      | 0 => -- First argument (Γ : List type)
        let param ← `(bracketedBinder| (Γ : List type))
        params := params.push param
      | 1 => -- Second argument (e : term)
        let param ← `(bracketedBinder| (e : term))
        params := params.push param
      | 2 => -- Third argument (τ : type)
        let param ← `(bracketedBinder| (t : type))
        params := params.push param
      | _ =>
        -- Handle additional arguments generically
        let paramName := mkIdent (Name.mkStr1 s!"arg{i}")
        let param ← `(bracketedBinder| ($paramName : _))
        params := params.push param

    -- Generate the complete function header
    let funHeader : TSyntax `command ←
      `(def $checkerIdent $params* : Option Bool := sorry)

    -- Elaborate the generated command
    elabCommand funHeader

  | _ => throwUnsupportedSyntax

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
