
module Prelude.Applicative where

open import Agda.Primitive
open import Prelude.Functor
open import Prelude.Function

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
