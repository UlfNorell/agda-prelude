
module Prelude.Ord where

open import Agda.Primitive
open import Prelude.Equality
open import Prelude.Decidable
open import Prelude.Bool
open import Prelude.Function

data Comparison {a} {A : Set a} (_<_ : A → A → Set a) (x y : A) : Set a where
  less    : x < y → Comparison _<_ x y
  equal   : x ≡ y → Comparison _<_ x y
  greater : y < x → Comparison _<_ x y

isLess : ∀ {a} {A : Set a} {R : A → A → Set a} {x y} → Comparison R x y → Bool
isLess (less    _) = true
isLess (equal   _) = false
isLess (greater _) = false

isGreater : ∀ {a} {A : Set a} {R : A → A → Set a} {x y} → Comparison R x y → Bool
isGreater (less    _) = false
isGreater (equal   _) = false
isGreater (greater _) = true

record Ord {a} (A : Set a) : Set (lsuc a) where
  field
    LessThan : A → A → Set a
    compare  : ∀ x y → Comparison LessThan x y

open Ord {{...}} public

_<_ : ∀ {a} {A : Set a} {{OrdA : Ord A}} → A → A → Bool
x < y = isLess (compare x y)

_>_ : ∀ {a} {A : Set a} {{OrdA : Ord A}} → A → A → Bool
_>_ = flip _<_

_≤_ : ∀ {a} {A : Set a} {{OrdA : Ord A}} → A → A → Bool
x ≤ y = not (y < x)

_≥_ : ∀ {a} {A : Set a} {{OrdA : Ord A}} → A → A → Bool
x ≥ y = not (x < y)

--- Instances ---

-- Generic instance by injection --

mapComparison : ∀ {a b} {A : Set a} {B : Set b} {LessA : A → A → Set a} {LessB : B → B → Set b}
                  {f : B → A} → (∀ {x y} → f x ≡ f y → x ≡ y) →
                  (∀ {x y} → LessA (f x) (f y) → LessB x y) →
                  ∀ {x y} → Comparison LessA (f x) (f y) → Comparison LessB x y
mapComparison _   g (less    p) = less (g p)
mapComparison inj g (equal   p) = equal (inj p)
mapComparison _   g (greater p) = greater (g p)

OrdBy : ∀ {a} {A B : Set a} {{OrdA : Ord A}} {f : B → A} →
          (∀ {x y} → f x ≡ f y → x ≡ y) → Ord B
OrdBy {f = f} inj = record { LessThan = LessThan on f
                           ; compare  = λ x y → mapComparison inj id (compare (f x) (f y))
                           }

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
OrdBool = record { LessThan = LessBool ; compare = compareBool }
