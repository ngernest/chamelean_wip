import Plausible.Sampleable
import Plausible.New.DeriveArbitrary
open Plausible

set_option linter.missingDocs false

/-- A datatype for binary trees -/
inductive Tree where
| Leaf : Tree
| Node : Nat → Tree → Tree → Tree
deriving Repr

/-- `balanced n t` describes whether the tree `t` of height `n` is *balanced*, i.e.
    every path through the tree has length either `n` or `n-1`. -/
inductive balanced : Nat → Tree → Prop where
| B0 : balanced 0 .Leaf
| B1 : balanced 1 .Leaf
| BS : ∀ n x l r,
  balanced n l → balanced n r →
  balanced (.succ n) (.Node x l r)

/-- `bst lo hi t` describes whether a tree `t` is a BST that contains values strictly within `lo` and `hi` -/
inductive bst : Nat → Nat → Tree → Prop where
| BstLeaf: bst lo hi .Leaf
| BstNode: ∀ lo hi x l r,
  lo < x →
  x < hi →
  bst lo x l →
  bst x hi r →
  bst lo hi (.Node x l r)

/-- Base types in the STLC (either Nat or functions) -/
inductive type where
  | Nat : type
  | Fun: type → type → type
  deriving BEq, DecidableEq, Repr

/-- Terms in the STLC extended with naturals and addition -/
inductive term where
  | Const: Nat → term
  | Add: term → term → term
  | Var: Nat → term
  | App: term → term → term
  | Abs: type → term → term
  deriving BEq, Repr

/-- `lookup Γ n τ` checks whether the `n`th element of the context `Γ` has type `τ` -/
inductive lookup : List type -> Nat -> type -> Prop where
  | LookupNow   : forall τ Γ, lookup (τ :: Γ) 0 τ
  | LookupLater : forall τ τ' n Γ,
      lookup Γ n τ -> lookup (τ' :: Γ) (.succ n) τ

/-- `typing Γ e τ` is the typing judgement `Γ ⊢ e : τ` -/
inductive typing: List type → term → type → Prop where
| TConst : ∀ n,
    typing Γ (.Const n) .Nat
| TAdd: ∀ e1 e2,
    typing Γ e1 .Nat →
    typing Γ e2 .Nat →
    typing Γ (.Add e1 e2) .Nat
| TAbs: ∀ e τ1 τ2,
    typing (τ1::Γ) e τ2 →
    typing Γ (.Abs τ1 e) (.Fun τ1 τ2)
| TVar: ∀ x τ,
    lookup Γ x τ →
    typing Γ (.Var x) τ
| TApp: ∀ e1 e2 τ1 τ2,
    typing Γ e2 τ1 →
    typing Γ e1 (.Fun τ1 τ2) →
    typing Γ (.App (.Abs .Nat e1) e2) τ2
