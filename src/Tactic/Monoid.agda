
module Tactic.Monoid where

open import Prelude
open import Tactic.Reflection
open import Tactic.Reflection.Quote

open import Structure.Monoid.Laws

open import Tactic.Monoid.Exp
open import Tactic.Monoid.Reflect
open import Tactic.Monoid.Proofs

monoidTactic : ∀ {a} {A : Set a} {{_ : Monoid A}} {{_ : MonoidLaws A}} → Tactic
monoidTactic {A = A} {{dict}} {{laws}} hole =
  do goal   ← inferType hole
  -| `A     ← quoteTC A
  -| catchTC (unify goal (def (quote _≡_) (hArg unknown ∷ hArg `A ∷ vArg unknown ∷ vArg unknown ∷ [])))
             (typeError $ strErr "Goal is not an equality" ∷ termErr goal ∷ [])
  ~| match  ← monoidMatcher dict
  -| `dict  ← quoteTC dict
  -| `laws  ← quoteTC laws
  -| caseM parseGoal match goal of λ
     { ((lhs , rhs) , env) →
       catchTC (unify hole (def (quote proof) (iArg `dict ∷ iArg `laws ∷ vArg (` lhs) ∷ vArg (` rhs) ∷
                                              vArg (quoteEnv `dict env) ∷ vArg (con (quote refl) []) ∷ [])))
               (typeError (strErr "Can't prove" ∷ termErr (` lhs) ∷ strErr "==" ∷ termErr (` rhs) ∷
                           strErr "because" ∷ termErr (` (flatten lhs)) ∷ strErr "/=" ∷ termErr (` (flatten rhs))
                           ∷ []))
     }

macro
  auto-monoid : ∀ {a} {A : Set a} {{Mon : Monoid A}} {{Laws : MonoidLaws A}} → Tactic
  auto-monoid {{Mon}} {{Laws}} = monoidTactic {{Mon}} {{Laws}}
