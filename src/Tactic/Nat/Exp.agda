
module Tactic.Nat.Exp where

open import Prelude

Var = Nat

Env : Set → Set
Env Atom = Atom → Nat

infixl 6 _⟨+⟩_
infixl 7 _⟨*⟩_
data Exp (Atom : Set) : Set where
  var : (x : Atom) → Exp Atom
  lit : (n : Nat) → Exp Atom
  _⟨+⟩_ _⟨*⟩_ : (e e₁ : Exp Atom) → Exp Atom

⟦_⟧e : ∀ {Atom} → Exp Atom → Env Atom → Nat
⟦ var x ⟧e   ρ = ρ x
⟦ lit n ⟧e   ρ = n
⟦ e₁ ⟨+⟩ e₂ ⟧e ρ = ⟦ e₁ ⟧e ρ + ⟦ e₂ ⟧e ρ
⟦ e₁ ⟨*⟩ e₂ ⟧e ρ = ⟦ e₁ ⟧e ρ * ⟦ e₂ ⟧e ρ

