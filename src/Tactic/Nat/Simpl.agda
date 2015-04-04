
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

simpl : List (Arg Type) → Term → Term
simpl _ = simplify-tactic

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

on-type-of-term : Name → Term → Term
on-type-of-term tac t =
  def (quote use)
    $ vArg t
    ∷ vArg (on-goal tac)
    ∷ []

macro
  follows-from : Term → Term
  follows-from = on-type-of-term (quote assumed-tactic)

  simplify : Term → Term
  simplify t =
    def (quote use)
      $ vArg t
      ∷ vArg (quote-goal $ abs "g" $
                unquote-term (def (quote simplify-tactic) (vArg (var 0 []) ∷ []))
                             (vArg (var 1 []) ∷ []))
      ∷ []

infixr -100 apply-tactic
syntax apply-tactic (λ _ → tac) (λ x → goal) = tac to x $ goal
apply-tactic : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → A → B
apply-tactic f x = f x
