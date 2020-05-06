
module Tactic.Monoid where

open import Prelude
open import Tactic.Reflection
open import Tactic.Reflection.Quote

open import Structure.Monoid.Laws

open import Tactic.Monoid.Exp
open import Tactic.Monoid.Reflect
open import Tactic.Monoid.Proofs

monoidTactic : ∀ {a} {A : Set a} {MonA : Monoid A} {{_ : MonoidLaws A {{MonA}}}} → Tactic
monoidTactic {A = A} {dict} {{laws}} hole = do
  goal   ← inferNormalisedType hole
  `A     ← quoteTC A
  unify goal (def (quote _≡_) (hArg unknown ∷ hArg `A ∷ vArg unknown ∷ vArg unknown ∷ []))
    <|> do typeErrorFmt "Goal is not an equality: %t" goal
  goal   ← normalise goal
  ensureNoMetas goal
  match  ← monoidMatcher dict
  `dict  ← quoteTC dict
  `laws  ← quoteTC laws
  ensureNoMetas `dict
  debugPrintFmt "tactic.monoid" 20 "monoidTactic %t, dict = %t" goal `dict
  (lhs , rhs) , env ← parseGoal match goal
  unify hole (def (quote proof) (iArg `dict ∷ iArg `laws ∷ vArg (` lhs) ∷ vArg (` rhs) ∷
                                 vArg (quoteEnv `dict env) ∷ vArg (con (quote refl) []) ∷ []))
    <|> do typeErrorFmt "Can't prove %t == %t because %t /= %t"
                        (` lhs) (` rhs) (` (flatten lhs)) (` (flatten rhs))

macro
  auto-monoid : ∀ {a} {A : Set a} {Mon : Monoid A} {{Laws : MonoidLaws A {{Mon}}}} → Tactic
  auto-monoid {{Laws}} = monoidTactic {{Laws}}
