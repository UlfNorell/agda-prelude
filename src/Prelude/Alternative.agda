
module Prelude.Alternative where

open import Agda.Primitive
open import Prelude.Maybe
open import Prelude.List
open import Prelude.String

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
