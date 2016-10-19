
module Prelude.Alternative where

open import Agda.Primitive
open import Prelude.Bool
open import Prelude.Maybe
open import Prelude.List
open import Prelude.Sum
open import Prelude.Decidable
open import Prelude.Functor
open import Prelude.Function
open import Prelude.Monoid

record Alternative {a b} (F : Set a → Set b) : Set (lsuc (a ⊔ b)) where
  infixl 3 _<|>_
  field
    empty : ∀ {A} → F A
    _<|>_ : ∀ {A} → F A → F A → F A
    overlap {{super}} : Functor F

open Alternative public using (super)
open Alternative {{...}} public

{-# DISPLAY Alternative.empty _     = empty   #-}
{-# DISPLAY Alternative._<|>_ _ x y = x <|> y #-}

instance
  -- Left-biased choice
  AlternativeMaybe : ∀ {a} → Alternative (Maybe {a})
  empty {{AlternativeMaybe}}           = nothing
  _<|>_ {{AlternativeMaybe}} nothing y = y
  _<|>_ {{AlternativeMaybe}} x       y = x
  super AlternativeMaybe = it

  AlternativeList : ∀ {a} → Alternative (List {a})
  empty {{AlternativeList}} = []
  _<|>_ {{AlternativeList}} = _++_
  super AlternativeList = it

  AlternativeEither : ∀ {a b} {E : Set b} {{_ : Monoid E}} → Alternative (Either {b = a} E)
  empty {{AlternativeEither}}     = left mempty
  _<|>_ {{AlternativeEither}} x y = either (const y) right x
  super AlternativeEither = it

module _ {a b} {F : Set a → Set b} {A : Set a} {{_ : Alternative F}} where
  guardA! : Bool → F A → F A
  guardA! true  x = x
  guardA! false _ = empty

  guardA : ∀ {p} {P : Set p} (d : Dec P) → ({{_ : P}} → F A) → F A
  guardA (yes p) x = x {{p}}
  guardA (no  _) _ = empty

  choice : List (F A) → F A
  choice = foldr _<|>_ empty
