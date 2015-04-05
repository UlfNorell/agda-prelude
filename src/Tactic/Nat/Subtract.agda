
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

private
  liftNFSubEq : ∀ e₁ e₂ ρ → ⟦ normSub e₁ ⟧sn ρ ≡ ⟦ normSub e₂ ⟧sn ρ → ⟦ e₁ ⟧se ρ ≡ ⟦ e₂ ⟧se ρ
  liftNFSubEq e₁ e₂ ρ eq = eraseEquality $ sound-sub e₁ ρ ⟨≡⟩ eq ⟨≡⟩ʳ sound-sub e₂ ρ

  unliftNFSubEq : ∀ e₁ e₂ ρ → ⟦ e₁ ⟧se ρ ≡ ⟦ e₂ ⟧se ρ → ⟦ normSub e₁ ⟧sn ρ ≡ ⟦ normSub e₂ ⟧sn ρ
  unliftNFSubEq e₁ e₂ ρ eq = eraseEquality $ sound-sub e₁ ρ ʳ⟨≡⟩ eq ⟨≡⟩ sound-sub e₂ ρ

autosub-proof : ∀ e₁ e₂ ρ → Maybe (⟦ e₁ ⟧se ρ ≡ ⟦ e₂ ⟧se ρ)
autosub-proof e₁ e₂ ρ with normSub e₁ == normSub e₂
autosub-proof e₁ e₂ ρ | no _   = nothing
autosub-proof e₁ e₂ ρ | yes eq = just (liftNFSubEq e₁ e₂ ρ (cong (λ n → ⟦ n ⟧sn ρ) eq))

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

--- Simplification ---

private
  SubExpEq : SubExp × SubExp → Env Var → Set
  SubExpEq (e₁ , e₂) ρ = ⟦ e₁ ⟧se ρ ≡ ⟦ e₂ ⟧se ρ

  CancelSubEq : SubExp × SubExp → Env Var → Set
  CancelSubEq (e₁ , e₂) ρ = NFEqS (cancel (normSub e₁) (normSub e₂)) (atomEnvS ρ)

  ⟦_⟧sh : List (SubExp × SubExp) → Env Var → Set
  ⟦ [] ⟧sh ρ = ⊥
  ⟦ h ∷ [] ⟧sh ρ = SubExpEq h ρ
  ⟦ h ∷ g  ⟧sh ρ = SubExpEq h ρ → ⟦ g ⟧sh ρ

  ⟦_⟧shs : List (SubExp × SubExp) → Env Var → Set
  ⟦ [] ⟧shs ρ = ⊥
  ⟦ h ∷ [] ⟧shs ρ = CancelSubEq h ρ
  ⟦ h ∷ g  ⟧shs ρ = CancelSubEq h ρ → ⟦ g ⟧shs ρ

  simplifySubEq : ∀ eq (ρ : Env Var) → CancelSubEq eq ρ → SubExpEq eq ρ
  simplifySubEq (e₁ , e₂) ρ H = liftNFSubEq e₁ e₂ ρ $
    lem-sub-eval-simp (normSub e₁) ρ ⟨≡⟩
    cancel-sound (normSub e₁) (normSub e₂) (atomEnvS ρ) H ⟨≡⟩ʳ
    lem-sub-eval-simp (normSub e₂) ρ

  complicateSubEq : ∀ eq ρ → SubExpEq eq ρ → CancelSubEq eq ρ
  complicateSubEq (e₁ , e₂) ρ H =
    cancel-complete (normSub e₁) (normSub e₂) (atomEnvS ρ) $
    lem-sub-eval-simp (normSub e₁) ρ ʳ⟨≡⟩
    unliftNFSubEq e₁ e₂ ρ H ⟨≡⟩
    lem-sub-eval-simp (normSub e₂) ρ

  simplifySubH : ∀ goal ρ → ⟦ goal ⟧shs ρ → ⟦ goal ⟧sh ρ
  simplifySubH []            ρ ()
  simplifySubH (h ∷ [])     ρ H = simplifySubEq h ρ H
  simplifySubH (h ∷ h₂ ∷ g) ρ H = λ H₁ → simplifySubH (h₂ ∷ g) ρ $ H (complicateSubEq h ρ H₁)

simplifysub-tactic : Term → Term
simplifysub-tactic t =
  case termToSubHyps t of
  λ { nothing → failedProof (quote invalidGoal) t
    ; (just (goal , Γ)) →
      def (quote simplifySubH)
        $ vArg (` goal)
        ∷ vArg (quotedEnv Γ)
        ∷ []
    }

assumedsub-tactic : Term → Term
assumedsub-tactic t =
  case termToSubHyps t of
  λ { nothing → failedProof (quote invalidGoal) t
    ; (just (goal , Γ)) →
      def (quote simplifySubH)
          ( vArg (` goal)
          ∷ vArg (quotedEnv Γ)
          ∷ vArg (def (quote id) [])
          ∷ [])
    }

macro
  autosub : Term
  autosub = on-goal (quote autosub-tactic)

  follows-from-sub : Term → Term
  follows-from-sub = on-type-of-term (quote assumedsub-tactic)

  simplifysub : Term → Term
  simplifysub = rewrite-argument-tactic (quote simplifysub-tactic)

  simplify-goal : Term
  simplify-goal = rewrite-goal-tactic (quote simplifysub-tactic)
