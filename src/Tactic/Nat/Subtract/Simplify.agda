
module Tactic.Nat.Subtract.Simplify where

open import Prelude hiding (abs)
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
open import Tactic.Nat.Less.Lemmas

simplifySubEqn : ∀ eqn ρ → c⟦ eqn ⟧eqn ρ → ⟦ eqn ⟧eqn ρ
simplifySubEqn (a :≡ b) = simplifySubEq a b
simplifySubEqn (a :< b) = simplifySubLess a b
 
complicateSubEqn : ∀ eqn ρ → ⟦ eqn ⟧eqn ρ → c⟦ eqn ⟧eqn ρ
complicateSubEqn (a :≡ b) = complicateSubEq a b
complicateSubEqn (a :< b) = complicateSubLess a b
 
⟦_⟧sh : List Eqn → Env Var → Set
⟦ [] ⟧sh ρ = ⊥
⟦ h ∷ [] ⟧sh ρ = ⟦ h ⟧eqn ρ
⟦ h ∷ g  ⟧sh ρ = ⟦ h ⟧eqn ρ → ⟦ g ⟧sh ρ
 
⟦_⟧shs : List Eqn → Env Var → Set
⟦ [] ⟧shs ρ = ⊥
⟦ h ∷ [] ⟧shs ρ = c⟦ h ⟧eqn ρ
⟦ h ∷ g  ⟧shs ρ = c⟦ h ⟧eqn ρ → ⟦ g ⟧shs ρ
 
simplifySubH : ∀ goal ρ → ⟦ goal ⟧shs ρ → ⟦ goal ⟧sh ρ
simplifySubH []            ρ ()
simplifySubH (h ∷ [])     ρ H = simplifySubEqn h ρ H
simplifySubH (h ∷ h₂ ∷ g) ρ H = λ H₁ → simplifySubH (h₂ ∷ g) ρ $ H (complicateSubEqn h ρ H₁)

simplifysub-tactic : Term → Type → TC Term
simplifysub-tactic prf g =
  inferType prf >>= λ h →
  let t = pi (vArg h) (abs "_" (weaken 1 g)) in
  caseM termToSubHyps t of
  λ { nothing → pure $ failedProof (quote invalidGoal) t
    ; (just (goal , Γ)) → pure $
      def (quote flip)
        $ vArg (def (quote simplifySubH)
                    ( vArg (` goal)
                    ∷ vArg (quotedEnv Γ) ∷ [] ))
        ∷ vArg prf ∷ []
    }

simplifygoal-tactic : Type → TC Term
simplifygoal-tactic t =
  caseM termToSubHyps t of λ
  { nothing → pure $ failedProof (quote invalidGoal) t
  ; (just (goal , Γ)) → pure $
      def (quote simplifySubH)
        $ vArg (` goal)
        ∷ vArg (quotedEnv Γ)
        ∷ []
  }
