
module Prelude.Ord where

open import Agda.Primitive
open import Prelude.Equality
open import Prelude.Decidable
open import Prelude.Bool
open import Prelude.Function

data Comparison {a} {A : Set a} (_<_ : A → A → Set a) (x y : A) : Set a where
  less    : (lt : x < y) → Comparison _<_ x y
  equal   : (eq : x ≡ y) → Comparison _<_ x y
  greater : (gt : y < x) → Comparison _<_ x y

isLess : ∀ {a} {A : Set a} {R : A → A → Set a} {x y} → Comparison R x y → Bool
isLess (less    _) = true
isLess (equal   _) = false
isLess (greater _) = false

isGreater : ∀ {a} {A : Set a} {R : A → A → Set a} {x y} → Comparison R x y → Bool
isGreater (less    _) = false
isGreater (equal   _) = false
isGreater (greater _) = true

record Ord {a} (A : Set a) : Set (lsuc a) where
  infix 4 _<_ _≤_
  field
    _<_ : A → A → Set a
    _≤_ : A → A → Set a
    compare   : ∀ x y → Comparison _<_ x y
    eq-to-leq : ∀ {x y} → x ≡ y → x ≤ y
    lt-to-leq : ∀ {x y} → x < y → x ≤ y

open Ord {{...}} public

module _ {a} {A : Set a} {{_ : Ord A}} where

  _>_ : A → A → Set a
  a > b = b < a

  _≥_ : A → A → Set a
  a ≥ b = b ≤ a

  infix 4 _>_ _≥_ _<?_ _≤?_ _>?_ _≥?_

  _<?_ : A → A → Bool
  x <? y = isLess (compare x y)

  _>?_ : A → A → Bool
  _>?_ = flip _<?_

  _≤?_ : A → A → Bool
  x ≤? y = not (y <? x)

  _≥?_ : A → A → Bool
  x ≥? y = not (x <? y)

  min : A → A → A
  min x y = if x <? y then x else y

  max : A → A → A
  max x y = if x >? y then x else y

--- Instances ---

-- Default implementation of _≤_ --

data LessEq {a} {A : Set a} (_<_ : A → A → Set a) (x y : A) : Set a where
  less  : x < y → LessEq _<_ x y
  equal : x ≡ y → LessEq _<_ x y

defaultOrd : ∀ {a} {A : Set a} {_<_ : A → A → Set a} → (∀ x y → Comparison _<_ x y) → Ord A
defaultOrd {_<_ = _<_} compare =
  record { _≤_ = LessEq _<_
         ; compare   = compare
         ; eq-to-leq = equal
         ; lt-to-leq = less
         }

-- Generic instance by injection --

mapComparison : ∀ {a b} {A : Set a} {B : Set b} {S : A → A → Set a} {T : B → B → Set b} {f : A → B} → 
                (∀ {x y} → S x y → T (f x) (f y)) → ∀ {x y} → Comparison S x y → Comparison T (f x) (f y)
mapComparison f (less lt)    = less (f lt)
mapComparison f (equal refl) = equal refl
mapComparison f (greater gt) = greater (f gt)

injectComparison : ∀ {a b} {A : Set a} {B : Set b} {LessA : A → A → Set a} {LessB : B → B → Set b}
                  {f : B → A} → (∀ {x y} → f x ≡ f y → x ≡ y) →
                  (∀ {x y} → LessA (f x) (f y) → LessB x y) →
                  ∀ {x y} → Comparison LessA (f x) (f y) → Comparison LessB x y
injectComparison _   g (less    p) = less (g p)
injectComparison inj g (equal   p) = equal (inj p)
injectComparison _   g (greater p) = greater (g p)

OrdBy : ∀ {a} {A B : Set a} {{OrdA : Ord A}} {f : B → A} →
          (∀ {x y} → f x ≡ f y → x ≡ y) → Ord B
OrdBy {f = f} inj = defaultOrd λ x y → injectComparison inj id (compare (f x) (f y))

-- Bool --

data LessBool : Bool → Bool → Set where
  false<true : LessBool false true

private
  compareBool : ∀ x y → Comparison LessBool x y
  compareBool false false = equal refl
  compareBool false true  = less false<true
  compareBool true false  = greater false<true
  compareBool true true   = equal refl

OrdBool : Ord Bool
OrdBool = defaultOrd compareBool
