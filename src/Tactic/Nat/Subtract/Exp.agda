
module Tactic.Nat.Subtract.Exp where

open import Prelude
open import Tactic.Nat.Exp
open import Tactic.Nat.NF

infixl 6 _⟨+⟩_ _⟨-⟩_
infixl 7 _⟨*⟩_

data SubExp : Set where
  var : (x : Var) → SubExp
  lit : (n : Nat) → SubExp
  _⟨+⟩_ _⟨-⟩_ _⟨*⟩_ : (a b : SubExp) → SubExp

⟦_⟧se : SubExp → Env → Nat
⟦ var x ⟧se    ρ = ρ x
⟦ lit n ⟧se    ρ = n
⟦ e₁ ⟨+⟩ e₂ ⟧se ρ = ⟦ e₁ ⟧se ρ + ⟦ e₂ ⟧se ρ
⟦ e₁ ⟨-⟩ e₂ ⟧se ρ = ⟦ e₁ ⟧se ρ - ⟦ e₂ ⟧se ρ
⟦ e₁ ⟨*⟩ e₂ ⟧se ρ = ⟦ e₁ ⟧se ρ * ⟦ e₂ ⟧se ρ

_-nf_ : NF → NF → Maybe NF
a -nf b =
  case cancel a b of λ
  { (x  , []) → just x
  ; ([] ,  _) → just []
  ; (_  ,  _) → nothing }

-- Only succeeds if all subtractions cancel out.
normSub : SubExp → Maybe NF
normSub (var x) = just [ 1 , [ x ] ]
normSub (lit 0) = just []
normSub (lit n) = just [ n , [] ]
normSub (e ⟨+⟩ e₁) = _+nf_ <$> normSub e <*> normSub e₁
normSub (e ⟨-⟩ e₁) = normSub e >>= λ v → normSub e₁ >>= λ v₁ → v -nf v₁
normSub (e ⟨*⟩ e₁) = _*nf_ <$> normSub e <*> normSub e₁
