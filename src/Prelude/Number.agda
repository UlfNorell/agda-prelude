
module Prelude.Number where

open import Agda.Builtin.FromNat public
open import Agda.Builtin.FromNeg public

NoNumConstraint : ∀ {a} {A : Set a} → Number A → Set a
NoNumConstraint Num = ∀ {n} → Number.Constraint Num n

NoNegConstraint : ∀ {a} {A : Set a} → Negative A → Set a
NoNegConstraint Neg = ∀ {n} → Negative.Constraint Neg n
