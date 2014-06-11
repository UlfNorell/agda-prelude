
module Prelude.Functor where

open import Agda.Primitive
open import Prelude.Function

record Functor {a b} (F : Set a → Set b) : Set (lsuc a ⊔ b) where
  infixl 4 _<$>_ _<$_
  field
    fmap : ∀ {A B} → (A → B) → F A → F B
  _<$>_ = fmap

  _<$_ : ∀ {A B} → A → F B → F A
  x <$ m = fmap (const x) m

open Functor {{...}} public
