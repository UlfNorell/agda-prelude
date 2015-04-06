
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
open import Tactic.Nat.Less.Lemmas

-- less-suc : ∀ {n} → 0 < suc n
-- less-suc {n} = diff n auto

⟦_⟧eqn : Eqn → Env Var → Set
⟦ e₁ :≡ e₂ ⟧eqn ρ = ⟦ e₁ ⟧se ρ ≡ ⟦ e₂ ⟧se ρ
⟦ e₁ :< e₂ ⟧eqn ρ = ⟦ e₁ ⟧se ρ < ⟦ e₂ ⟧se ρ

autosub-proof : ∀ eqn ρ → Maybe (⟦ eqn ⟧eqn ρ)
autosub-proof (e₁ :≡ e₂) ρ with normSub e₁ == normSub e₂
autosub-proof (e₁ :≡ e₂) ρ | no _   = nothing
autosub-proof (e₁ :≡ e₂) ρ | yes eq = just (liftNFSubEq e₁ e₂ ρ (cong (λ n → ⟦ n ⟧sn ρ) eq))
autosub-proof (e₁ :< e₂) ρ with cancel (normSub e₁) (normSub e₂) | simplifySubLess e₁ e₂ ρ
autosub-proof (e₁ :< e₂) ρ | [] , (suc n , []) ∷ nf | simp =
  let sk : SubNF
      sk = (suc n , []) ∷ nf
      k  = (    n , []) ∷ nf in
  just $ simp $ diff (⟦ k ⟧sns ρ) $
    ns-sound sk (atomEnvS ρ) ⟨≡⟩
    auto ⟨≡⟩ʳ (λ z → suc (z + 0)) $≡ lem-eval-sns-nS k ρ
autosub-proof (e₁ :< e₂) ρ | _  , _ | simp = nothing

autosub-tactic : Term → Term
autosub-tactic t =
  case termToSubEqn t of
  λ { nothing → failedProof (quote invalidGoal) t
    ; (just (eqn , Γ)) →
      getProof (quote cantProve) t $
        def (quote autosub-proof)
            ( vArg (` eqn)
            ∷ vArg (quotedEnv Γ)
            ∷ [] )
    }

--- Simplification ---

private

  SubExpEqn : Eqn → Env Var → Set
  SubExpEqn (a :≡ b) = SubExpEq a b
  SubExpEqn (a :< b) = SubExpLess a b

  CancelSubEqn : Eqn → Env Var → Set
  CancelSubEqn (a :≡ b) = CancelSubEq a b
  CancelSubEqn (a :< b) = CancelSubLess a b

  simplifySubEqn : ∀ eqn ρ → CancelSubEqn eqn ρ → SubExpEqn eqn ρ
  simplifySubEqn (a :≡ b) = simplifySubEq a b
  simplifySubEqn (a :< b) = simplifySubLess a b

  complicateSubEqn : ∀ eqn ρ → SubExpEqn eqn ρ → CancelSubEqn eqn ρ
  complicateSubEqn (a :≡ b) = complicateSubEq a b
  complicateSubEqn (a :< b) = complicateSubLess a b

  ⟦_⟧sh : List Eqn → Env Var → Set
  ⟦ [] ⟧sh ρ = ⊥
  ⟦ h ∷ [] ⟧sh ρ = SubExpEqn h ρ
  ⟦ h ∷ g  ⟧sh ρ = SubExpEqn h ρ → ⟦ g ⟧sh ρ

  ⟦_⟧shs : List Eqn → Env Var → Set
  ⟦ [] ⟧shs ρ = ⊥
  ⟦ h ∷ [] ⟧shs ρ = CancelSubEqn h ρ
  ⟦ h ∷ g  ⟧shs ρ = CancelSubEqn h ρ → ⟦ g ⟧shs ρ

  simplifySubH : ∀ goal ρ → ⟦ goal ⟧shs ρ → ⟦ goal ⟧sh ρ
  simplifySubH []            ρ ()
  simplifySubH (h ∷ [])     ρ H = simplifySubEqn h ρ H
  simplifySubH (h ∷ h₂ ∷ g) ρ H = λ H₁ → simplifySubH (h₂ ∷ g) ρ $ H (complicateSubEqn h ρ H₁)

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

data Impossible : Set where

invalidEquation : ⊤
invalidEquation = _

private
  0≠suc : ∀ n → 0 ≡ suc n → ⊥
  0≠suc n ()

  n≮0 : ∀ {n} → n < 0 → ⊥
  n≮0 (diff k ())

  lem-refute : ∀ n nf ρ → 0 ≡ ⟦ (suc n , []) ∷ nf ⟧ns (atomEnvS ρ) → ⊥
  lem-refute n nf ρ eq = erase-⊥ $ 0≠suc (n + ⟦ nf ⟧n (atomEnvS ρ)) $
    eq ⟨≡⟩ ns-sound ((suc n , []) ∷ nf) (atomEnvS ρ) ⟨≡⟩ auto

refutation-proof : ∀ {a} {A : Set a} eqn ρ → Maybe (SubExpEqn eqn ρ → A)
refutation-proof (a :≡ b) ρ with cancel (normSub a) (normSub b) | complicateSubEq a b ρ
refutation-proof (a :≡ b) ρ | [] , (suc n , []) ∷ v | compl = just λ eq → ⊥-elim $ lem-refute n v ρ (compl eq)
refutation-proof (a :≡ b) ρ | (suc n , []) ∷ v , [] | compl = just λ eq → ⊥-elim $ lem-refute n v ρ (sym (compl eq))
refutation-proof (a :≡ b) ρ | _ , _ | _ = nothing

refutation-proof (a :< b) ρ with cancel (normSub a) (normSub b) | complicateSubLess a b ρ
refutation-proof (a :< b) ρ | v , [] | compl = just λ eq → ⊥-elim $ erase-⊥ $ n≮0 (compl eq)
refutation-proof (a :< b) ρ | _ , _  | _     = nothing

refutesub-tactic : Term → Term
refutesub-tactic (pi (vArg (el _ a)) _) =
  case termToSubEqn a of λ
  { nothing → failedProof (quote invalidEquation) a
  ; (just (eqn , Γ)) →
    getProof (quote cantProve) a $
    def (quote refutation-proof)
        $ vArg (` eqn)
        ∷ vArg (quotedEnv Γ)
        ∷ []
  }
refutesub-tactic _ = def (quote Impossible) []

macro
  autosub : Term
  autosub = on-goal (quote autosub-tactic)

  follows-from-sub : Term → Term
  follows-from-sub = on-type-of-term (quote assumedsub-tactic)

  simplifysub : Term → Term
  simplifysub = rewrite-argument-tactic (quote simplifysub-tactic)

  simplify-goal : Term
  simplify-goal = rewrite-goal-tactic (quote simplifysub-tactic)

  refutesub : Term → Term
  refutesub = on-type-of-term (quote refutesub-tactic)
