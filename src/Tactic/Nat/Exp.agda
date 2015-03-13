
module Tactic.Nat.Exp where

open import Prelude

Var = Nat

Env : Set
Env = Var → Nat

infixl 6 _⟨+⟩_
infixl 7 _⟨*⟩_
data Exp : Set where
  var : Var → Exp
  lit : Nat → Exp
  _⟨+⟩_ _⟨*⟩_ : Exp → Exp → Exp

⟦_⟧e : Exp → Env → Nat
⟦ var x ⟧e   ρ = ρ x
⟦ lit n ⟧e   ρ = n
⟦ e₁ ⟨+⟩ e₂ ⟧e ρ = ⟦ e₁ ⟧e ρ + ⟦ e₂ ⟧e ρ
⟦ e₁ ⟨*⟩ e₂ ⟧e ρ = ⟦ e₁ ⟧e ρ * ⟦ e₂ ⟧e ρ

