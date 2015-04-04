
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


macro
  autosub : Term
  autosub = on-goal (quote autosub-tactic)

test : ∀ a b → 0 - (a + b) ≡ 0 - a - b
test a b = autosub