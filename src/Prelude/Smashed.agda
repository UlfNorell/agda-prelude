
module Prelude.Smashed where

open import Prelude.Equality
open import Prelude.Unit
open import Prelude.Empty
open import Prelude.Nat.Core
open import Prelude.Function
open import Prelude.Ord

record Smashed {a} (A : Set a) : Set a where
  field
    smashed : ∀ {x y : A} → x ≡ y

open Smashed {{...}} public
{-# DISPLAY Smashed.smashed _ = smashed #-}

instance
  Smash⊤ : Smashed ⊤
  smashed {{Smash⊤}} = refl

  Smash⊥ : Smashed ⊥
  smashed {{Smash⊥}} {}

  Smash≡ : ∀ {a} {A : Set a} {a b : A} → Smashed (a ≡ b)
  smashed {{Smash≡}} {x = refl} {refl} = refl

-- Can't be instance, since this would interfere with the ⊤ and ⊥ instances.
SmashNonZero : ∀ {n : Nat} → Smashed (NonZero n)
SmashNonZero {zero}  = it
SmashNonZero {suc n} = it
