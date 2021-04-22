
module Tactic.Nat.Less.Lemmas where

open import Prelude

open import Tactic.Nat.Exp
open import Tactic.Nat.NF
open import Tactic.Nat.Subtract.Exp
open import Tactic.Nat.Auto.Lemmas
open import Tactic.Nat.Simpl.Lemmas
open import Tactic.Nat.Subtract.Lemmas

liftNFSubLess : ∀ e₁ e₂ ρ → ⟦ normSub e₁ ⟧sn ρ < ⟦ normSub e₂ ⟧sn ρ → ⟦ e₁ ⟧se ρ < ⟦ e₂ ⟧se ρ
liftNFSubLess e₁ e₂ ρ (diff k eq) = diff k (eraseEquality $
  sound-sub e₂ ρ ⟨≡⟩ eq ⟨≡⟩ʳ (suc k +_) $≡ sound-sub e₁ ρ)

SubExpLess : SubExp → SubExp → Env Var → Set
SubExpLess e₁ e₂ ρ = ⟦ e₁ ⟧se ρ < ⟦ e₂ ⟧se ρ

NFLessS : SubNF × SubNF → Env SubAtom → Set
NFLessS (nf₁ , nf₂) ρ = ⟦ nf₁ ⟧ns ρ < ⟦ nf₂ ⟧ns ρ

CancelSubLess : SubExp → SubExp → Env Var → Set
CancelSubLess e₁ e₂ ρ = NFLessS (cancel (normSub e₁) (normSub e₂)) (atomEnvS ρ)

c⟦_⟧eqn : Eqn → Env Var → Set
c⟦ a :≡ b ⟧eqn = CancelSubEq a b
c⟦ a :< b ⟧eqn = CancelSubLess a b

simplifySubLess : ∀ e₁ e₂ (ρ : Env Var) → CancelSubLess e₁ e₂ ρ → SubExpLess e₁ e₂ ρ
simplifySubLess e₁ e₂ ρ H with cancel (normSub e₁) (normSub e₂)
                             | (λ a b → cancel-sound′ a b (normSub e₁) (normSub e₂) (atomEnvS ρ))
simplifySubLess e₁ e₂ ρ (diff k H) | v₁ , v₂ | sound =
  liftNFSubLess e₁ e₂ ρ $ diff k $
    lem-eval-sn-nS (normSub e₂) ρ ⟨≡⟩
    sound (suc k) 0
      ((suc k +_) $≡ ns-sound v₁ (atomEnvS ρ) ʳ⟨≡⟩
       H ʳ⟨≡⟩ ns-sound v₂ (atomEnvS ρ)) ʳ⟨≡⟩ʳ
    (suc k +_) $≡ lem-eval-sn-nS (normSub e₁) ρ

complicateSubLess : ∀ e₁ e₂ ρ → SubExpLess e₁ e₂ ρ → CancelSubLess e₁ e₂ ρ
complicateSubLess e₁ e₂ ρ H with cancel (normSub e₁) (normSub e₂)
                                   | (λ a b → cancel-complete′ a b (normSub e₁) (normSub e₂) (atomEnvS ρ))
complicateSubLess e₁ e₂ ρ (diff k H) | v₁ , v₂ | complete = diff k (eraseEquality $
  ns-sound v₂ (atomEnvS ρ) ⟨≡⟩
  complete (suc k) 0
    ((suc k +_) $≡ lem-eval-sn-nS (normSub e₁) ρ ʳ⟨≡⟩
     (suc k +_) $≡ sound-sub e₁ ρ ʳ⟨≡⟩
     H ʳ⟨≡⟩ sound-sub e₂ ρ ⟨≡⟩
     lem-eval-sn-nS (normSub e₂) ρ) ʳ⟨≡⟩ʳ
  (suc k +_) $≡ ns-sound v₁ (atomEnvS ρ))
