
module Tactic.Nat.Simpl where

open import Prelude
open import Builtin.Reflection
open import Tactic.Reflection.Quote
open import Tactic.Reflection

open import Tactic.Nat.Reflect
open import Tactic.Nat.NF
open import Tactic.Nat.Exp
open import Tactic.Nat.Auto
open import Tactic.Nat.Auto.Lemmas
open import Tactic.Nat.Simpl.Lemmas

use : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
use x f = f x

ExpEq : Exp × Exp → Env → Set
ExpEq (e₁ , e₂) ρ = ⟦ e₁ ⟧e ρ ≡ ⟦ e₂ ⟧e ρ

CancelEq : Exp × Exp → Env → Set
CancelEq (e₁ , e₂) ρ = NFEqS (cancel (norm e₁) (norm e₂)) ρ

⟦_⟧h : List (Exp × Exp) → Env → Set
⟦ [] ⟧h ρ = ⊥
⟦ h ∷ [] ⟧h ρ = ExpEq h ρ
⟦ h ∷ g  ⟧h ρ = ExpEq h ρ → ⟦ g ⟧h ρ

⟦_⟧hs : List (Exp × Exp) → Env → Set
⟦ [] ⟧hs ρ = ⊥
⟦ h ∷ [] ⟧hs ρ = CancelEq h ρ
⟦ h ∷ g  ⟧hs ρ = CancelEq h ρ → ⟦ g ⟧hs ρ

simplify : ∀ eq ρ → CancelEq eq ρ → ExpEq eq ρ
simplify (e₁ , e₂) ρ H = liftNFEq e₁ e₂ ρ (cancel-sound (norm e₁) (norm e₂) ρ H)

complicate : ∀ eq ρ → ExpEq eq ρ → CancelEq eq ρ
complicate (e₁ , e₂) ρ H =
  cancel-complete (norm e₁) (norm e₂) ρ
  (unliftNFEq e₁ e₂ ρ H)

simplifyH : ∀ goal ρ → ⟦ goal ⟧hs ρ → ⟦ goal ⟧h ρ
simplifyH []            ρ ()
simplifyH (h ∷ [])     ρ H = simplify h ρ H
simplifyH (h ∷ h₂ ∷ g) ρ H = λ H₁ → simplifyH (h₂ ∷ g) ρ $ H (complicate h ρ H₁)

simpl : List (Arg Type) → Term → Term
simpl _ t =
  case termToHyps t of
  λ { nothing → failedProof (quote invalidGoal) t
    ; (just (goal , Γ)) →
      def (quote simplifyH) ( vArg (` goal)
                            ∷ vArg (quotedEnv Γ)
                            ∷ [])
    }


assumed-tactic : Term → Term
assumed-tactic t =
  case termToHyps t of
  λ { nothing → failedProof (quote invalidGoal) t
    ; (just (goal , Γ)) →
      def (quote simplifyH) ( vArg (` goal)
                            ∷ vArg (quotedEnv Γ)
                            ∷ vArg (def (quote id) [])
                            ∷ [])
    }

macro
  follows-from : Term → Term
  follows-from t =
    def (quote use)
      $ vArg t
      ∷ vArg (on-goal (quote assumed-tactic))
      ∷ []
