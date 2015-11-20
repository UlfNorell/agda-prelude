
module Prelude.Number where

open import Agda.Primitive
open import Prelude.Nat.Core

record Number {a} (A : Set a) : Set (lsuc a) where
  field
    Constraint : Nat → Set a
    fromNat : ∀ n → {{_ : Constraint n}} → A

  NoConstraint : Set a
  NoConstraint = ∀ {n} → Constraint n

open Number {{...}} public using (fromNat)

{-# BUILTIN FROMNAT fromNat #-}
{-# DISPLAY Number.fromNat _ n = fromNat n #-}

record Negative {a} (A : Set a) : Set (lsuc a) where
  field
    Constraint : Nat → Set a
    fromNeg : ∀ n → {{_ : Constraint n}} → A

  NoConstraint : Set a
  NoConstraint = ∀ {n} → Constraint n

open Negative {{...}} public using (fromNeg)

{-# BUILTIN FROMNEG fromNeg #-}
{-# DISPLAY Negative.fromNeg _ n = fromNeg n #-}
