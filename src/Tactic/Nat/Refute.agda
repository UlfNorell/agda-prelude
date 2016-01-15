
module Tactic.Nat.Refute where

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
open import Tactic.Nat.Simpl

data Impossible : Set where

invalidEquation : ⊤
invalidEquation = _

refutation : ∀ {a} {A : Set a} {Atom : Set} {{_ : Eq Atom}} {{_ : Ord Atom}} eq (ρ : Env Atom) →
               ¬ CancelEq eq ρ → ExpEq eq ρ → A
refutation exp ρ !eq eq = ⊥-elim (!eq (complicateEq exp ρ eq))

refute-tactic : Term → TC Term
refute-tactic prf =
  inferType prf >>= λ a →
  caseM termToEq (unEl a) of λ
  { nothing → pure $ failedProof (quote invalidEquation) (unEl a)
  ; (just (eqn , Γ)) → pure $
    def (quote refutation)
        $ vArg (` eqn)
        ∷ vArg (quotedEnv Γ)
        ∷ vArg absurd-lam
        ∷ vArg prf ∷ []
  }

macro
  refute : Term → Tactic
  refute prf hole = unify hole =<< refute-tactic prf
