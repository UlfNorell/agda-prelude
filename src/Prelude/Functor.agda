
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

-- Level polymorphic functors
record Functor′ {a b} (F : ∀ {a} → Set a → Set a) : Set (lsuc (a ⊔ b)) where
  infixl 4 _<$>′_ _<$′_
  field
    fmap′ : {A : Set a} {B : Set b} → (A → B) → F A → F B
  _<$>′_ = fmap′

  _<$′_ : {A : Set a} {B : Set b} → B → F A → F B
  x <$′ m = fmap′ (const x) m

open Functor′ {{...}} public

infixr 0 flip-fmap
syntax flip-fmap a (λ x → y) = for x ← a do y
flip-fmap : ∀ {a b} {F : Set a → Set b} {{_ : Functor F}} {A B} → F A → (A → B) → F B
flip-fmap x f = fmap f x

infixr 0 caseF_of_
caseF_of_ : ∀ {a b} {F : Set a → Set b} {{_ : Functor F}} {A B} → F A → (A → B) → F B
caseF_of_ x f = fmap f x

-- Congruence for _<$>_ --

infixl 4 _=$=_ _=$=′_
_=$=_ : ∀ {a b} {A B : Set a} {F : Set a → Set b} {{_ : Functor F}} {x y : F A}
          (f : A → B) → x ≡ y → (f <$> x) ≡ (f <$> y)
f =$= refl = refl

_=$=′_ : ∀ {a b} {A : Set a} {B : Set b} {F : ∀ {a} → Set a → Set a} {{_ : Functor′ F}} {x y : F A}
          (f : A → B) → x ≡ y → (f <$>′ x) ≡ (f <$>′ y)
f =$=′ refl = refl
