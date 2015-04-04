
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

refute-tactic : Term → Term
refute-tactic (pi (vArg (el _ a)) _) =
  case termToEq a of λ
  { nothing → failedProof (quote invalidEquation) a
  ; (just (eq , Γ)) →
    def (quote refutation)
        $ vArg (` eq)
        ∷ vArg (quotedEnv Γ)
        ∷ vArg absurd-lam
        ∷ []
  }
refute-tactic _ = def (quote Impossible) []

macro
  refute : Term → Term
  refute t =
    def (quote use)
      $ vArg t
      ∷ vArg (on-goal (quote refute-tactic))
      ∷ []
