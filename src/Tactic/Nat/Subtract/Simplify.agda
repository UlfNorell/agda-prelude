
module Tactic.Nat.Subtract.Simplify where

open import Prelude
open import Builtin.Reflection
open import Tactic.Reflection.Quote
open import Tactic.Reflection.DeBruijn
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
simplifygoal-tactic (el _ (pi _ (abs _ (el _ t)))) =
  case strengthen 1 t of λ
  { nothing → typeErrorS "simplify-goal must be applied in a non-dependent function position"
  ; (just t) →
    caseM termToSubHyps t of λ
    { nothing → pure $ failedProof (quote invalidGoal) t
    ; (just (goal , Γ)) → pure $
        def (quote simplifySubH)
          $ vArg (` goal)
          ∷ vArg (quotedEnv Γ)
          ∷ []
    }
  }
simplifygoal-tactic _ = typeErrorS "simplify-goal must be applied in a function position"

private
  el! : Term → Type
  el! v = el unknown v

  set₀ : Type
  set₀ = el! (agda-sort (lit 0))

-- TODO: move to library
forceFun : Type → TC Type
forceFun (el s a) =
  newMeta (el unknown (agda-sort unknown)) >>= λ dom →
  newMeta (el unknown (agda-sort unknown)) >>= λ rng →
  unify a (pi (vArg (el! dom)) (abs "_" (el! $ weaken 1 rng))) >>
  el s <$> normalise a

macro
  simplify-goal : Tactic
  simplify-goal hole =
    do goal ← forceFun =<< inferType hole
    -| unify hole =<< simplifygoal-tactic goal

  simplifysub : Term → Tactic
  simplifysub prf hole =
    caseM forceFun =<< inferType hole of λ
    { (el _ (pi _ (abs _ goal))) →
      flip (maybe (typeErrorS "Should be non-dependent function")) (strengthen 1 goal) λ goal →
      unify hole =<< simplifysub-tactic prf goal
    ; _ → typeErrorS "Invalid goal"
    }

private
  test-goal : (a b c : Nat) → a ≡ c → a + b ≡ b + c
  test-goal a b c eq = simplify-goal eq

  test-simp : (a b c : Nat) → a + b ≡ b + c → 2 + a ≡ 1 + c + 1
  test-simp a b c eq = simplifysub eq λ eq′ → eq′
