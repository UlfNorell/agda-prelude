
module Tactic.Nat.Coprime.Problem where

open import Prelude
open import Container.List
open import Numeric.Nat.GCD

Atom = Nat

infixl 7 _⊗_
infix  3 _⋈_
infix  2 _⊨_

data Exp : Set where
  atom : (x : Atom) → Exp
  _⊗_ : (a b : Exp) → Exp

data Formula : Set where
  _⋈_ : (a b : Exp) → Formula

data Problem : Set where
  _⊨_ : (Γ : List Formula) (φ : Formula) → Problem

Env = Atom → Nat

⟦_⟧e_ : Exp → Env → Nat
⟦ atom x ⟧e ρ = ρ x
⟦ e ⊗ e₁ ⟧e ρ = ⟦ e ⟧e ρ * ⟦ e₁ ⟧e ρ

⟦_⟧f_ : Formula → Env → Set
⟦ a ⋈ b ⟧f ρ = Coprime (⟦ a ⟧e ρ) (⟦ b ⟧e ρ)

⟦_⟧p'_ : Problem → Env → Set
⟦ Γ ⊨ φ ⟧p' ρ = All (⟦_⟧f ρ) Γ → ⟦ φ ⟧f ρ

⟦_⟧p_ : Problem → Env → Set
⟦ Γ ⊨ φ ⟧p ρ = foldr (λ ψ A → ⟦ ψ ⟧f ρ → A) (⟦ φ ⟧f ρ) Γ

curryProblem : ∀ Q ρ → ⟦ Q ⟧p' ρ → ⟦ Q ⟧p ρ
curryProblem ([]    ⊨ φ) ρ H = H []
curryProblem (x ∷ Γ ⊨ φ) ρ H = λ x → curryProblem (Γ ⊨ φ) ρ (H ∘ (x ∷_))
