
module Prelude.Alternative where

open import Agda.Primitive
open import Prelude.Bool
open import Prelude.Maybe
open import Prelude.List
open import Prelude.Decidable

record Alternative {a b} (F : Set a → Set b) : Set (lsuc (a ⊔ b)) where
  infixl 3 _<|>_
  field
    empty : ∀ {A} → F A
    _<|>_ : ∀ {A} → F A → F A → F A

open Alternative {{...}} public

{-# DISPLAY Alternative.empty _     = empty   #-}
{-# DISPLAY Alternative._<|>_ _ x y = x <|> y #-}

instance
  -- Left-biased choice
  AlternativeMaybe : ∀ {a} → Alternative (Maybe {a})
  empty {{AlternativeMaybe}}           = nothing
  _<|>_ {{AlternativeMaybe}} nothing y = y
  _<|>_ {{AlternativeMaybe}} x       y = x

  AlternativeList : ∀ {a} → Alternative (List {a})
  empty {{AlternativeList}} = []
  _<|>_ {{AlternativeList}} = _++_

module _ {a b} {F : Set a → Set b} {A : Set a} {{_ : Alternative F}} where
  guardA! : Bool → F A → F A
  guardA! true  x = x
  guardA! false _ = empty

  guardA : ∀ {p} {P : Set p} (d : Dec P) → ({{_ : P}} → F A) → F A
  guardA (yes p) x = x {{p}}
  guardA (no  _) _ = empty

  choice : List (F A) → F A
  choice = foldr _<|>_ empty
