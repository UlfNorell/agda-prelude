
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

module _ {Atom : Set} {{_ : Eq Atom}} {{_ : Ord Atom}} where
  ExpEq : Exp Atom × Exp Atom → Env Atom → Set
  ExpEq (e₁ , e₂) ρ = ⟦ e₁ ⟧e ρ ≡ ⟦ e₂ ⟧e ρ

  CancelEq : Exp Atom × Exp Atom → Env Atom → Set
  CancelEq (e₁ , e₂) ρ = NFEqS (cancel (norm e₁) (norm e₂)) ρ

  ⟦_⟧h : List (Exp Atom × Exp Atom) → Env Atom → Set
  ⟦ [] ⟧h ρ = ⊥
  ⟦ h ∷ [] ⟧h ρ = ExpEq h ρ
  ⟦ h ∷ g  ⟧h ρ = ExpEq h ρ → ⟦ g ⟧h ρ

  ⟦_⟧hs : List (Exp Atom × Exp Atom) → Env Atom → Set
  ⟦ [] ⟧hs ρ = ⊥
  ⟦ h ∷ [] ⟧hs ρ = CancelEq h ρ
  ⟦ h ∷ g  ⟧hs ρ = CancelEq h ρ → ⟦ g ⟧hs ρ

  simplifyEq : ∀ eq (ρ : Env Atom) → CancelEq eq ρ → ExpEq eq ρ
  simplifyEq (e₁ , e₂) ρ H = liftNFEq e₁ e₂ ρ (cancel-sound (norm e₁) (norm e₂) ρ H)

  complicateEq : ∀ eq ρ → ExpEq eq ρ → CancelEq eq ρ
  complicateEq (e₁ , e₂) ρ H =
    cancel-complete (norm e₁) (norm e₂) ρ
    (unliftNFEq e₁ e₂ ρ H)

  simplifyH : ∀ goal ρ → ⟦ goal ⟧hs ρ → ⟦ goal ⟧h ρ
  simplifyH []            ρ ()
  simplifyH (h ∷ [])     ρ H = simplifyEq h ρ H
  simplifyH (h ∷ h₂ ∷ g) ρ H = λ H₁ → simplifyH (h₂ ∷ g) ρ $ H (complicateEq h ρ H₁)

simplify-tactic : Term → Term
simplify-tactic t =
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
  follows-from = on-type-of-term (quote assumed-tactic)

  simplify : Term → Term
  simplify = rewrite-argument-tactic (quote simplify-tactic)
