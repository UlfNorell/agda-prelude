module Prelude.Semigroup where


open import Prelude.Function
open import Prelude.Maybe

open import Prelude.List

open import Prelude.Semiring
open import Prelude.Applicative
open import Prelude.Functor
open import Prelude.Equality

record Semigroup {a} (A : Set a) : Set a where
  infixr 6 _<>_
  field
    _<>_ : A → A → A
open Semigroup {{...}} public

{-# DISPLAY Semigroup._<>_ _ a b = a <> b #-}
{-# DISPLAY Semigroup._<>_ _ = _<>_ #-}

record Semigroup/Laws {a} (A : Set a) : Set a where
  field
    {{super}} : Semigroup A
    semigroup-assoc : (a b c : A) → (a <> b) <> c ≡ a <> (b <> c)
open Semigroup/Laws {{...}} public hiding (super)

instance
  SemigroupList : ∀ {a} {A : Set a} → Semigroup (List A)
  _<>_   {{SemigroupList}} = _++_

  SemigroupFun : ∀ {a b} {A : Set a} {B : A → Set b} {{_ : ∀ {x} → Semigroup (B x)}} → Semigroup (∀ x → B x)
  _<>_   {{SemigroupFun}} f g x = f x <> g x

  SemigroupMaybe : ∀ {a} {A : Set a} → Semigroup (Maybe A)
  _<>_   {{SemigroupMaybe}} nothing  y = y
  _<>_   {{SemigroupMaybe}} (just x) _ = just x
