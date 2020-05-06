
module Prelude.Alternative where

open import Agda.Primitive
open import Prelude.Bool
open import Prelude.Maybe
open import Prelude.List
open import Prelude.Sum
open import Prelude.Decidable
open import Prelude.Functor
open import Prelude.Applicative
open import Prelude.Function
open import Prelude.Monoid
open import Prelude.Variables renaming (ℓ₁ to a; ℓ₂ to b)

module _ (F : Set a → Set b) where
  record FunctorZero : Set (lsuc a ⊔ b) where
    field
      empty : ∀ {A} → F A
      overlap {{super}} : Functor F

  record Alternative : Set (lsuc a ⊔ b) where
    infixl 3 _<|>_
    field
      _<|>_ : ∀ {A} → F A → F A → F A
      overlap {{super}} : FunctorZero

open FunctorZero {{...}} public

open Alternative {{...}} public

{-# DISPLAY FunctorZero.empty _     = empty   #-}
{-# DISPLAY Alternative._<|>_ _ x y = x <|> y #-}

instance
  FunctorZeroMaybe : FunctorZero (Maybe {a})
  empty {{FunctorZeroMaybe}} = nothing

  -- Left-biased choice
  AlternativeMaybe : Alternative (Maybe {a})
  _<|>_ {{AlternativeMaybe}} nothing y = y
  _<|>_ {{AlternativeMaybe}} x       y = x

  FunctorZeroList : FunctorZero (List {a})
  empty {{FunctorZeroList}} = []

  AlternativeList : Alternative (List {a})
  _<|>_ {{AlternativeList}} = _++_

  FunctorZeroEither : ⦃ Monoid A ⦄ → FunctorZero (Either {b = a} A)
  empty {{FunctorZeroEither}}     = left mempty

  AlternativeEither : ⦃ Monoid A ⦄ → Alternative (Either {b = a} A)
  _<|>_ {{AlternativeEither}} x y = either (const y) right x

module _ ⦃ _ : FunctorZero F ⦄ where

  guard! : Bool → F A → F A
  guard! true  x = x
  guard! false _ = empty

  guard : (d : Dec A) → (⦃ A ⦄ → F B) → F B
  guard (yes p) x = x ⦃ p ⦄
  guard (no  _) _ = empty

module _ ⦃ _ : Alternative F ⦄ where

  choice : List (F A) → F A
  choice = foldr _<|>_ empty

  maybeA : ⦃ Applicative F ⦄ → F A → F (Maybe A)
  maybeA x = just <$> x <|> pure nothing
