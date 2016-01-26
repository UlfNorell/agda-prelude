
module Data.Monoid.Laws where

open import Prelude
open import Data.Monoid

record MonoidLaws {a} (A : Set a) {{Mon : Monoid A}} : Set a where
  field
    idLeft  : (x : A)     → mempty <> x ≡ x
    idRight : (x : A)     → x <> mempty ≡ x
    <>assoc : (x y z : A) → x <> (y <> z) ≡ (x <> y) <> z

open MonoidLaws {{...}} public

{-# DISPLAY MonoidLaws.idLeft _ = idLeft   #-}
{-# DISPLAY MonoidLaws.idRight _ = idRight #-}
{-# DISPLAY MonoidLaws.<>assoc _ = <>assoc #-}

instance
  MonoidLawsList : ∀ {a} {A : Set a} → MonoidLaws (List A)
  idLeft  {{MonoidLawsList}} xs       = refl
  idRight {{MonoidLawsList}} []       = refl
  idRight {{MonoidLawsList}} (x ∷ xs) = x ∷_ $≡ idRight xs
  <>assoc {{MonoidLawsList}} []       ys zs = refl
  <>assoc {{MonoidLawsList}} (x ∷ xs) ys zs = x ∷_ $≡ <>assoc xs ys zs

  MonoidLawsMaybe : ∀ {a} {A : Set a} {{_ : Monoid A}} {{_ : MonoidLaws A}} → MonoidLaws (Maybe A)
  idLeft  {{MonoidLawsMaybe}} x     = refl
  idRight {{MonoidLawsMaybe}} nothing  = refl
  idRight {{MonoidLawsMaybe}} (just _) = refl
  <>assoc {{MonoidLawsMaybe}} nothing  y z = refl
  <>assoc {{MonoidLawsMaybe}} (just x) nothing  z = refl
  <>assoc {{MonoidLawsMaybe}} (just x) (just y) nothing  = refl
  <>assoc {{MonoidLawsMaybe}} (just x) (just y) (just z) = just $≡ <>assoc x y z

  -- Can't do function lifting because no extentionality.
