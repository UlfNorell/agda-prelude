module Prelude.Ord where

open import Agda.Primitive
open import Prelude.Equality
open import Prelude.Decidable
open import Prelude.Bool
open import Prelude.Function
open import Prelude.Empty
open import Prelude.Variables

data Comparison {a} {A : Set a} (_<_ : A → A → Set a) (x y : A) : Set a where
  less    : (lt : x < y) → Comparison _<_ x y
  equal   : (eq : x ≡ y) → Comparison _<_ x y
  greater : (gt : y < x) → Comparison _<_ x y

isLess : ∀ {a} {A : Set a} {R : A → A → Set a} {x y} → Comparison R x y → Bool
isLess (less    _) = true
isLess (equal   _) = false
isLess (greater _) = false
{-# INLINE isLess #-}

isGreater : ∀ {a} {A : Set a} {R : A → A → Set a} {x y} → Comparison R x y → Bool
isGreater (less    _) = false
isGreater (equal   _) = false
isGreater (greater _) = true
{-# INLINE isGreater #-}

infixr 0 comparison-elim
syntax comparison-elim c (λ lt → x) (λ eq → y) (λ gt → z) =
  case-cmp c less    lt => x
             equal   eq => y
             greater gt => z

-- The termination checker can't handle merge-like functions using 'with'.
-- Use this instead.
comparison-elim : {_<_ : A → A → Set _} →
                  Comparison _<_ x y →
                  (x < y → B) →
                  (x ≡ y → B) →
                  (y < x → B) → B
comparison-elim (less    p) lt eq gt = lt p
comparison-elim (equal   p) lt eq gt = eq p
comparison-elim (greater p) lt eq gt = gt p
{-# INLINE comparison-elim #-}

data LessEq {a} {A : Set a} (_<_ : A → A → Set a) (x y : A) : Set a where
  less  : x < y → LessEq _<_ x y
  equal : x ≡ y → LessEq _<_ x y

record Ord {a} (A : Set a) : Set (lsuc a) where
  infix 4 _<_ _≤_
  field
    _<_ : A → A → Set a
    _≤_ : A → A → Set a
    compare     : ∀ x y → Comparison _<_ x y
    eq-to-leq   : ∀ {x y} → x ≡ y → x ≤ y
    lt-to-leq   : ∀ {x y} → x < y → x ≤ y
    leq-to-lteq : ∀ {x y} → x ≤ y → LessEq _<_ x y

open Ord {{...}} public

{-# DISPLAY Ord._<_ _ a b = a < b #-}
{-# DISPLAY Ord._≤_ _ a b = a ≤ b #-}
{-# DISPLAY Ord.compare     _ a b = compare a b #-}
{-# DISPLAY Ord.eq-to-leq   _ eq = eq-to-leq eq #-}
{-# DISPLAY Ord.lt-to-leq   _ eq = lt-to-leq eq #-}
{-# DISPLAY Ord.leq-to-lteq _ eq = leq-to-lteq eq #-}

module _ {a} {A : Set a} {{_ : Ord A}} where

  _>_ : A → A → Set a
  a > b = b < a

  _≥_ : A → A → Set a
  a ≥ b = b ≤ a

  _≮_ : A → A → Set a
  a ≮ b = ¬ (a < b)

  _≯_ : A → A → Set a
  _≯_ = flip _≮_

  _≰_ : A → A → Set a
  a ≰ b = ¬ (a ≤ b)

  _≱_ : A → A → Set a
  _≱_ = flip _≰_

  infix 4 _>_ _≥_ _≮_ _≯_ _≰_ _≱_
          _<?_ _≤?_ _>?_ _≥?_
          _≮?_ _≯?_ _≰?_ _≱?_

  _<?_ : A → A → Bool
  x <? y = isLess (compare x y)

  _>?_ : A → A → Bool
  _>?_ = flip _<?_

  _≤?_ : A → A → Bool
  x ≤? y = not (y <? x)

  _≥?_ : A → A → Bool
  x ≥? y = not (x <? y)

  _≮?_ : A → A → Bool
  _≮?_ = _≥?_

  _≯?_ : A → A → Bool
  _≯?_ = flip _≮?_

  _≰?_ : A → A → Bool
  _≰?_ = _>?_

  _≱?_ : A → A → Bool
  _≱?_ = flip _≰?_

  min : A → A → A
  min x y = if x <? y then x else y

  max : A → A → A
  max x y = if x >? y then x else y

  {-# INLINE _>?_ #-}
  {-# INLINE _<?_ #-}
  {-# INLINE _≤?_ #-}
  {-# INLINE _≥?_ #-}
  {-# INLINE min #-}
  {-# INLINE max #-}

--- Instances ---

-- Default implementation of _≤_ --

defaultOrd : ∀ {a} {A : Set a} {_<_ : A → A → Set a} → (∀ x y → Comparison _<_ x y) → Ord A
Ord._<_         (defaultOrd compare) = _
Ord._≤_        (defaultOrd {_<_ = _<_} compare) = LessEq _<_
Ord.compare     (defaultOrd compare) = compare
Ord.eq-to-leq   (defaultOrd compare) = equal
Ord.lt-to-leq   (defaultOrd compare) = less
Ord.leq-to-lteq (defaultOrd compare) = id

-- Generic instance by injection --

module _ {a b} {A : Set a} {B : Set b} {S : A → A → Set a} {T : B → B → Set b} where

  mapComparison : {f : A → B} →
                  (∀ {x y} → S x y → T (f x) (f y)) →
                  ∀ {x y} → Comparison S x y → Comparison T (f x) (f y)
  mapComparison f (less lt)    = less (f lt)
  mapComparison f (equal refl) = equal refl
  mapComparison f (greater gt) = greater (f gt)

  injectComparison : {f : B → A} → (∀ {x y} → f x ≡ f y → x ≡ y) →
                     (∀ {x y} → S (f x) (f y) → T x y) →
                     ∀ {x y} → Comparison S (f x) (f y) → Comparison T x y
  injectComparison _   g (less    p) = less (g p)
  injectComparison inj g (equal   p) = equal (inj p)
  injectComparison _   g (greater p) = greater (g p)

flipComparison : ∀ {a} {A : Set a} {S : A → A → Set a} {x y} →
                 Comparison S x y → Comparison (flip S) x y
flipComparison (less    lt) = greater lt
flipComparison (equal   eq) = equal   eq
flipComparison (greater gt) = less    gt

OrdBy : ∀ {a} {A B : Set a} {{OrdA : Ord A}} {f : B → A} →
          (∀ {x y} → f x ≡ f y → x ≡ y) → Ord B
OrdBy {f = f} inj = defaultOrd λ x y → injectComparison inj id (compare (f x) (f y))

{-# INLINE OrdBy #-}
{-# INLINE defaultOrd #-}
{-# INLINE injectComparison #-}

-- Bool --

data LessBool : Bool → Bool → Set where
  false<true : LessBool false true

private
  compareBool : ∀ x y → Comparison LessBool x y
  compareBool false false = equal refl
  compareBool false true  = less false<true
  compareBool true false  = greater false<true
  compareBool true true   = equal refl

instance
  OrdBool : Ord Bool
  OrdBool = defaultOrd compareBool

--- Ord with proofs ---

record Ord/Laws {a} (A : Set a) : Set (lsuc a) where
  field
    overlap {{super}} : Ord A
    less-antirefl : {x : A} → x < x → ⊥
    less-trans    : {x y z : A} → x < y → y < z → x < z

open Ord/Laws {{...}} public hiding (super)

module _ {a} {A : Set a} {{OrdA : Ord/Laws A}} where

  less-antisym  : {x y : A} → x < y → y < x → ⊥
  less-antisym lt lt₁ = less-antirefl {A = A} (less-trans {A = A} lt lt₁)

  leq-antisym : {x y : A} → x ≤ y → y ≤ x → x ≡ y
  leq-antisym x≤y y≤x with leq-to-lteq {A = A} x≤y | leq-to-lteq {A = A} y≤x
  ... | _          | equal refl = refl
  ... | less x<y   | less y<x   = ⊥-elim (less-antisym x<y y<x)
  ... | equal refl | less _     = refl

  leq-trans : {x y z : A} → x ≤ y → y ≤ z → x ≤ z
  leq-trans x≤y y≤z with leq-to-lteq {A = A} x≤y | leq-to-lteq {A = A} y≤z
  ... | equal refl | _          = y≤z
  ... | _          | equal refl = x≤y
  ... | less x<y   | less y<z   = lt-to-leq {A = A} (less-trans {A = A} x<y y<z)

  leq-less-antisym : {x y : A} → x ≤ y → y < x → ⊥
  leq-less-antisym {x = x} {y} x≤y y<x =
    case leq-antisym x≤y (lt-to-leq {A = A} y<x) of λ where
      refl → less-antirefl {A = A} y<x


OrdLawsBy : ∀ {a} {A B : Set a} {{OrdA : Ord/Laws A}} {f : B → A} →
              (∀ {x y} → f x ≡ f y → x ≡ y) → Ord/Laws B
Ord/Laws.super (OrdLawsBy inj)        = OrdBy inj
less-antirefl {{OrdLawsBy {A = A} _}} = less-antirefl {A = A}
less-trans    {{OrdLawsBy {A = A} _}} = less-trans    {A = A}

instance
  OrdLawsBool : Ord/Laws Bool
  Ord/Laws.super OrdLawsBool = it
  less-antirefl {{OrdLawsBool}} ()
  less-trans    {{OrdLawsBool}} false<true ()


module _ {ℓ} {A : Set ℓ} {{OrdA : Ord/Laws A}} where

  _≤-dec_ : (a b : A) → Dec (a ≤ b)
  _≤-dec_ a b
    with compare a b
  ...| less a<b = yes (lt-to-leq {ℓ} a<b)
  ...| equal a≡b = yes (eq-to-leq a≡b)
  ...| greater a>b = no (λ x → leq-less-antisym {ℓ} x a>b)

  _<-dec_ : (a b : A) → Dec (a < b)
  _<-dec_ a b
    with compare a b
  ...| less a<b = yes a<b
  ...| equal a≡b rewrite a≡b = no (less-antirefl {ℓ})
  ...| greater a>b = no (λ x → less-antisym {ℓ} x a>b)

  infix 4 _<-dec_ _≤-dec_
