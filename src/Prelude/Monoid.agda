module Prelude.Monoid where

open import Prelude.Function
open import Prelude.Maybe

open import Prelude.List

open import Prelude.Semiring
open import Prelude.Semigroup public

open import Prelude.Applicative
open import Prelude.Functor
open import Prelude.Equality

open import Prelude.Variables

record Monoid {a} (A : Set a) : Set a where
  field
    {{super}} : Semigroup A
    mempty : A
open Monoid {{...}} public hiding (super)

{-# DISPLAY Monoid.mempty _ = mempty #-}


record Monoid/Laws {ℓ} (A : Set ℓ) : Set ℓ where
  field
    overlap {{super}} : Monoid A
    left-identity : (e : A) → mempty <> e ≡ e
    right-identity : (e : A) → e <> mempty ≡ e
    -- Using Semigroup/Laws instance creates inference problems
    monoid-assoc : (a b c : A) → (a <> b) <> c ≡ a <> (b <> c)
open Monoid/Laws {{...}} public hiding (super)


mconcat : ∀ {a} {A : Set a} {{MonA : Monoid A}} → List A → A
mconcat = foldr _<>_ mempty

--- Instances ---

instance

  MonoidList : ∀ {a} {A : Set a} → Monoid (List A)
  Monoid.super MonoidList = it
  mempty {{MonoidList}} = []

  MonoidFun : ∀ {a b} {A : Set a} {B : A → Set b} {{_ : ∀ {x} → Monoid (B x)}} → Monoid (∀ x → B x)
  Monoid.super (MonoidFun {a} {b} {A} {B} {{SG}}) =
    SemigroupFun {a} {b} {A} {B} {{Monoid.super SG}}
  mempty {{MonoidFun}} _ = mempty

  MonoidMaybe : ∀ {a} {A : Set a} → Monoid (Maybe A)
  Monoid.super MonoidMaybe = it
  mempty {{MonoidMaybe}} = nothing

record Sum {a} (A : Set a) : Set a where
  constructor mkSum
  field getSum : A
open Sum public

instance
  SemigroupSum : ∀ {a} {A : Set a} {{_ : Semiring A}} → Semigroup (Sum A)
  getSum (_<>_   {{SemigroupSum}} x y) = getSum x + getSum y

  MonoidSum : ∀ {a} {A : Set a} {{_ : Semiring A}} → Monoid (Sum A)
  Monoid.super MonoidSum = it
  getSum (mempty {{MonoidSum}}) = zro

record Product {a} (A : Set a) : Set a where
  constructor mkProduct
  field getProduct : A

open Product public

instance
  SemigroupProduct : ∀ {a} {A : Set a} {{_ : Semiring A}} → Semigroup (Product A)
  getProduct (_<>_   {{SemigroupProduct}} x y) = getProduct x * getProduct y

  MonoidProduct : ∀ {a} {A : Set a} {{_ : Semiring A}} → Monoid (Product A)
  Monoid.super MonoidProduct = it
  getProduct (mempty {{MonoidProduct}}) = one

record Const {a b} (A : Set a) (B : Set b) : Set a where
  constructor mkConst
  field getConst : A

open Const public

module _ {a b} {A : Set a} {{MonA : Monoid A}} where
  instance
    FunctorConst : Functor {a = b} (Const A)
    getConst (fmap {{FunctorConst}} f x) = getConst x

    ApplicativeConst : Applicative (Const A)
    getConst (pure  {{ApplicativeConst}} x)     = mempty
    getConst (_<*>_ {{ApplicativeConst}} wf wx) = getConst wf <> getConst wx
