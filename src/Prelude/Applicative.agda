
module Prelude.Applicative where

open import Agda.Primitive
open import Prelude.Functor
open import Prelude.Function
open import Prelude.Equality

record Applicative {a b} (F : Set a → Set b) : Set (lsuc a ⊔ b) where
  infixl 4 _<*>_ _<*_ _*>_
  field
    pure  : ∀ {A} → A → F A
    _<*>_ : ∀ {A B} → F (A → B) → F A → F B

  defaultApplicativeFunctor : Functor F
  defaultApplicativeFunctor = record { fmap = λ f x → pure f <*> x }

  _<*_ : ∀ {A B} → F A → F B → F A
  a <* b = pure const <*> a <*> b

  _*>_ : ∀ {A B} → F A → F B → F B
  a *> b = pure (const id) <*> a <*> b

open Applicative {{...}} public

-- Congruence for _<*>_ and friends

infixl 4 _=*=_
_=*=_ : ∀ {a b} {A B : Set a} {F : Set a → Set b} {{_ : Applicative F}} {f g : F (A → B)} {x y : F A} →
          f ≡ g → x ≡ y → (f <*> x) ≡ (g <*> y)
refl =*= refl = refl

_=*_ : ∀ {a b} {A B : Set a} {F : Set a → Set b} {{_ : Applicative F}} {a₁ a₂ : F A} {b₁ b₂ : F B} →
         a₁ ≡ a₂ → b₁ ≡ b₂ → (a₁ <* b₁) ≡ (a₂ <* b₂)
refl =* refl = refl

_*=_ : ∀ {a b} {A B : Set a} {F : Set a → Set b} {{_ : Applicative F}} {a₁ a₂ : F A} {b₁ b₂ : F B} →
         a₁ ≡ a₂ → b₁ ≡ b₂ → (a₁ *> b₁) ≡ (a₂ *> b₂)
refl *= refl = refl
