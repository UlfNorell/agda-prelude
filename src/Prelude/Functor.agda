
module Prelude.Functor where

open import Agda.Primitive
open import Prelude.Function
open import Prelude.Equality

record Functor {a b} (F : Set a → Set b) : Set (lsuc a ⊔ b) where
  infixl 4 _<$>_ _<$_
  field
    fmap : ∀ {A B} → (A → B) → F A → F B
  _<$>_ = fmap

  _<$_ : ∀ {A B} → A → F B → F A
  x <$ m = fmap (const x) m

open Functor {{...}} public

-- Congruence for _<$>_ --

infixl 4 _=$=_ 
_=$=_ : ∀ {a b} {A B : Set a} {F : Set a → Set b} {{_ : Functor F}} {x y : F A}
          (f : A → B) → x ≡ y → (f <$> x) ≡ (f <$> y)
f =$= refl = refl
