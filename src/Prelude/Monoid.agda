
module Prelude.Monoid where

open import Prelude.Maybe
open import Prelude.List
open import Prelude.Semiring
open import Prelude.Applicative

record Monoid {a} (A : Set a) : Set a where
  infixr 6 _<>_
  field
    mempty : A
    _<>_   : A → A → A

open Monoid {{...}} public

{-# DISPLAY Monoid.mempty _ = mempty #-}
{-# DISPLAY Monoid._<>_ _ a b = a <> b #-}

mconcat : ∀ {a} {A : Set a} {{MonA : Monoid A}} → List A → A
mconcat = foldr _<>_ mempty

--- Instances ---

instance
  MonoidList : ∀ {a} {A : Set a} → Monoid (List A)
  mempty {{MonoidList}} = []
  _<>_   {{MonoidList}} = _++_

  MonoidFun : ∀ {a b} {A : Set a} {B : A → Set b} {{_ : ∀ {x} → Monoid (B x)}} → Monoid (∀ x → B x)
  mempty {{MonoidFun}}     _ = mempty
  _<>_   {{MonoidFun}} f g x = f x <> g x

  MonoidMaybe : ∀ {a} {A : Set a} → Monoid (Maybe A)
  mempty {{MonoidMaybe}} = nothing
  _<>_   {{MonoidMaybe}} nothing  y = y
  _<>_   {{MonoidMaybe}} (just x) _ = just x

record Sum {a} (A : Set a) : Set a where
  constructor mkSum
  field getSum : A

open Sum public

instance
  MonoidSum : ∀ {a} {A : Set a} {{_ : Semiring A}} → Monoid (Sum A)
  getSum (mempty {{MonoidSum}})     = zro
  getSum (_<>_   {{MonoidSum}} x y) = getSum x + getSum y

record Product {a} (A : Set a) : Set a where
  constructor mkProduct
  field getProduct : A

open Product public

instance
  MonoidProduct : ∀ {a} {A : Set a} {{_ : Semiring A}} → Monoid (Product A)
  getProduct (mempty {{MonoidProduct}})     = one
  getProduct (_<>_   {{MonoidProduct}} x y) = getProduct x * getProduct y

record Const {a b} (A : Set a) (B : Set b) : Set a where
  constructor mkConst
  field getConst : A

open Const public

instance
  ApplicativeConst : ∀ {a b} {A : Set a} {{MonA : Monoid A}} → Applicative {a = b} (Const A)
  getConst (pure  {{ApplicativeConst}} x)     = mempty
  getConst (_<*>_ {{ApplicativeConst}} wf wx) = getConst wf <> getConst wx
