
module Data.Monoid where

open import Prelude

record Monoid {a} (A : Set a) : Set a where
  infixr 6 _<>_
  field
    mempty : A
    _<>_   : A → A → A

open Monoid {{...}} public

mconcat : ∀ {a} {A : Set a} {{MonA : Monoid A}} → List A → A
mconcat = foldr _<>_ mempty

--- Instances ---

MonoidList : ∀ {a} {A : Set a} → Monoid (List A)
MonoidList = record { mempty = [] ; _<>_ = _++_ }

MonoidFun : ∀ {a} {A : Set a} → Monoid (A → A)
MonoidFun = record { mempty = id ; _<>_ = λ f g → f ∘ g }

record SumNat : Set where
  constructor mkSum
  field getSum : Nat

open SumNat public

MonoidSum : Monoid SumNat
MonoidSum = record { mempty = mkSum 0 ; _<>_ = λ n m → mkSum (getSum n + getSum m) }

record ProductNat : Set where
  constructor mkProduct
  field getProduct : Nat

open ProductNat public

MonoidProduct : Monoid ProductNat
MonoidProduct = record { mempty = mkProduct 1 ; _<>_ = λ n m → mkProduct (getProduct n * getProduct m) }

record Const {a b} (A : Set a) (B : Set b) : Set a where
  constructor mkConst
  field getConst : A

open Const public

ApplicativeConst : ∀ {a b} {A : Set a} {{MonA : Monoid A}} → Applicative {a = b} (Const A)
ApplicativeConst = record { pure  = const (mkConst mempty)
                          ; _<*>_ = λ wf wx → mkConst (getConst wf <> getConst wx) }
