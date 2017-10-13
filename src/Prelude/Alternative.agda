
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

module _ {a b} (F : Set a → Set b) where
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
  FunctorZeroMaybe : ∀ {a} → FunctorZero (Maybe {a})
  empty {{FunctorZeroMaybe}} = nothing

  -- Left-biased choice
  AlternativeMaybe : ∀ {a} → Alternative (Maybe {a})
  _<|>_ {{AlternativeMaybe}} nothing y = y
  _<|>_ {{AlternativeMaybe}} x       y = x

  FunctorZeroList : ∀ {a} → FunctorZero (List {a})
  empty {{FunctorZeroList}} = []

  AlternativeList : ∀ {a} → Alternative (List {a})
  _<|>_ {{AlternativeList}} = _++_

  FunctorZeroEither : ∀ {a b} {E : Set b} {{_ : Monoid E}} → FunctorZero (Either {b = a} E)
  empty {{FunctorZeroEither}}     = left mempty

  AlternativeEither : ∀ {a b} {E : Set b} {{_ : Monoid E}} → Alternative (Either {b = a} E)
  _<|>_ {{AlternativeEither}} x y = either (const y) right x

module _ {a b} {F : Set a → Set b} {A : Set a} {{_ : FunctorZero F}} where
  guard! : Bool → F A → F A
  guard! true  x = x
  guard! false _ = empty

  guard : ∀ {p} {P : Set p} (d : Dec P) → ({{_ : P}} → F A) → F A
  guard (yes p) x = x {{p}}
  guard (no  _) _ = empty

module _ {a b} {F : Set a → Set b} {A : Set a} {{_ : Alternative F}} where
  choice : List (F A) → F A
  choice = foldr _<|>_ empty

  maybeA : {{_ : Applicative F}} → F A → F (Maybe A)
  maybeA x = just <$> x <|> pure nothing
