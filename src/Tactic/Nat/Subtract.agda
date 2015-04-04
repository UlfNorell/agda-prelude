
module Tactic.Nat.Subtract where

open import Prelude
open import Builtin.Reflection
open import Tactic.Reflection.Quote
open import Tactic.Reflection
open import Control.Monad.State

open import Tactic.Nat.Reflect
open import Tactic.Nat.NF
open import Tactic.Nat.Exp
open import Tactic.Nat.Auto
open import Tactic.Nat.Auto.Lemmas
open import Tactic.Nat.Simpl.Lemmas
open import Tactic.Nat.Simpl
open import Tactic.Nat.Reflect

open import Tactic.Nat.Subtract.Exp
open import Tactic.Nat.Subtract.Reflect
open import Tactic.Nat.Subtract.Lemmas

NormEq : Maybe (NF Var) → Maybe (NF Var) → Env Var → Set
NormEq nothing _ _ = ⊥
NormEq _ nothing _ = ⊥
NormEq (just n) (just n₁) ρ = ⟦ n ⟧n ρ ≡ ⟦ n₁ ⟧n ρ

private
  liftSubNFEq′ : ∀ e₁ e₂ ρ → NormEq (normSub e₁) (normSub e₂) ρ → ⟦ e₁ ⟧se ρ ≡ ⟦ e₂ ⟧se ρ
  liftSubNFEq′ e₁ e₂ ρ nfEq with normSub e₁ | normSub e₂ | sound-sub e₁ ρ | sound-sub e₂ ρ
  ... | nothing | _       | sound₁ | sound₂ = ⊥-elim nfEq
  ... | just _  | nothing | sound₁ | sound₂ = ⊥-elim nfEq
  ... | just n₁ | just n₂ | sound₁ | sound₂ = sound₁ ⟨≡⟩ nfEq ⟨≡⟩ʳ sound₂

liftSubNFEq : ∀ e₁ e₂ ρ → NormEq (normSub e₁) (normSub e₂) ρ → ⟦ e₁ ⟧se ρ ≡ ⟦ e₂ ⟧se ρ
liftSubNFEq e₁ e₂ ρ normEq = eraseEquality $ liftSubNFEq′ e₁ e₂ ρ normEq

autosub-proof : ∀ e₁ e₂ ρ → Maybe (⟦ e₁ ⟧se ρ ≡ ⟦ e₂ ⟧se ρ)
autosub-proof e₁ e₂ ρ with normSub e₁ | normSub e₂ | liftSubNFEq e₁ e₂
autosub-proof e₁ e₂ ρ | nothing | _       | _  = nothing
autosub-proof e₁ e₂ ρ | _       | nothing | _  = nothing
autosub-proof e₁ e₂ ρ | just n  | just n₁ | liftEq with n == n₁
autosub-proof e₁ e₂ ρ | just n  | just n₁ | liftEq | no _ = nothing
autosub-proof e₁ e₂ ρ | just n  | just n₁ | liftEq | yes nfeq = just (liftEq ρ (cong (λ n → ⟦ n ⟧n ρ) nfeq))

autosub-tactic : Term → Term
autosub-tactic t =
  case termToSubEq t of
  λ { nothing → failedProof (quote invalidGoal) t
    ; (just ((e₁ , e₂) , Γ)) →
      def (quote getProof)
        $ vArg (def (quote autosub-proof)
                    ( vArg (` e₁)
                    ∷ vArg (` e₂)
                    ∷ vArg (quotedEnv Γ)
                    ∷ []))
        ∷ vArg (def (quote cantProve) $ vArg (stripImplicit t) ∷ [])
        ∷ []
    }

macro
  autosub : Term
  autosub = on-goal (quote autosub-tactic)
