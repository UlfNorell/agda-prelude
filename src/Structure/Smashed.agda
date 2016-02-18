
module Structure.Smashed where

open import Prelude

record Smashed {a} (A : Set a) : Set a where
  field
    smashed : ∀ {x y : A} → x ≡ y

open Smashed {{...}} public
{-# DISPLAY Smashed.smashed _ = smashed #-}

instance
  Smash⊤ : Smashed ⊤
  Smash⊤ = record { smashed = refl }

  Smash⊥ : Smashed ⊥
  Smash⊥ = record { smashed = λ {} }

  Smash≡ : ∀ {a} {A : Set a} {a b : A} → Smashed (a ≡ b)
  Smashed.smashed Smash≡ {x = refl} {refl} = refl

-- Can't be instance, since this would interfere with the ⊤ and ⊥ instances.
SmashNonZero : ∀ {n : Nat} → Smashed (NonZero n)
SmashNonZero {zero}  = it
SmashNonZero {suc n} = it
