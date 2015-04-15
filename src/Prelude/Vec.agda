
module Prelude.Vec where

open import Prelude.Nat
open import Prelude.Fin
open import Prelude.Function
open import Prelude.Functor
open import Prelude.Applicative
open import Prelude.List
open import Prelude.Equality
open import Prelude.Decidable
open import Prelude.Ord
open import Prelude.Semiring

infixr 5 _∷_
data Vec {a} (A : Set a) : Nat → Set a where
  []  : Vec A zero
  _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)

private
  -- These are private. Use pure and _<*>_ instead.
  vec : ∀ {a} {A : Set a} {n} → A → Vec A n
  vec {n = zero } x = []
  vec {n = suc n} x = x ∷ vec x

  vapp : ∀ {a b} {A : Set a} {B : Set b} {n} → Vec (A → B) n → Vec A n → Vec B n
  vapp  []       _       = []
  vapp (f ∷ fs) (x ∷ xs) = f x ∷ vapp fs xs

vecToList : ∀ {a} {A : Set a} {n} → Vec A n → List A
vecToList []       = []
vecToList (x ∷ xs) = x ∷ vecToList xs

listToVec : ∀ {a} {A : Set a} (xs : List A) → Vec A (length xs)
listToVec []       = []
listToVec (x ∷ xs) = x ∷ listToVec xs

--- Lookup ---

indexVec : ∀ {a} {A : Set a} {n} → Vec A n → Fin n → A
indexVec (x ∷ xs) zero    = x
indexVec (x ∷ xs) (suc i) = indexVec xs i

tabulate : ∀ {a} {A : Set a} {n} → (Fin n → A) → Vec A n
tabulate {n = zero } f = []
tabulate {n = suc n} f = f zero ∷ tabulate (f ∘ suc)

--- Folding ---

vfoldr : ∀ {a b} {A : Set a} {B : Nat → Set b} → (∀ {n} → A → B n → B (suc n)) → B 0 → ∀ {n} → Vec A n → B n
vfoldr f z [] = z
vfoldr f z (x ∷ xs) = f x (vfoldr (λ {n} → f {n}) z xs)

vfoldl : ∀ {a b} {A : Set a} {B : Nat → Set b} → (∀ {n} → B n → A → B (suc n)) → B 0 → ∀ {n} → Vec A n → B n
vfoldl         f z [] = z
vfoldl {B = B} f z (x ∷ xs) = vfoldl {B = B ∘ suc} f (f z x) xs

--- Other list functions ---

module _ {a} {A : Set a} where

  infixr 5 _v++_
  _v++_ : ∀ {m n} → Vec A m → Vec A n → Vec A (m + n)
  []       v++ ys = ys
  (x ∷ xs) v++ ys = x ∷ xs v++ ys 

  vreverse : ∀ {n} → Vec A n → Vec A n
  vreverse xs = vfoldl {B = Vec A} (flip _∷_) [] xs

--- Equality ---

vcons-inj-head : ∀ {a} {A : Set a} {x y : A} {n}
                   {xs ys : Vec A n} → x Vec.∷ xs ≡ y ∷ ys → x ≡ y
vcons-inj-head refl = refl

vcons-inj-tail : ∀ {a} {A : Set a} {x y : A} {n}
                   {xs ys : Vec A n} → x Vec.∷ xs ≡ y ∷ ys → xs ≡ ys
vcons-inj-tail refl = refl

private
  eqVec : ∀ {a} {A : Set a} {{EqA : Eq A}} {n} (xs ys : Vec A n) → Dec (xs ≡ ys)
  eqVec [] []             = yes refl
  eqVec (x ∷ xs) (y ∷ ys) with x == y
  eqVec (x ∷ xs) (y ∷ ys)    | no neq   = no λ eq → neq (vcons-inj-head eq)
  eqVec (x ∷ xs) (.x ∷ ys)   | yes refl with eqVec xs ys
  eqVec (x ∷ xs) (.x ∷ ys)   | yes refl    | no neq = no λ eq → neq (vcons-inj-tail eq)
  eqVec (x ∷ xs) (.x ∷ .xs)  | yes refl    | yes refl = yes refl

instance
  EqVec : ∀ {a} {A : Set a} {{EqA : Eq A}} {n} → Eq (Vec A n)
  EqVec = record { _==_ = eqVec }

--- Ord ---

data LessVec {a} {A : Set a} {{OrdA : Ord A}} : ∀ {n} → Vec A n → Vec A n → Set a where
  head< : ∀ {x y n} {xs ys : Vec A n} → x < y → LessVec (x ∷ xs) (y ∷ ys)
  tail< : ∀ {x n} {xs ys : Vec A n}   → LessVec xs ys → LessVec (x ∷ xs) (x ∷ ys)

private
  compareVec : ∀ {a} {A : Set a} {{OrdA : Ord A}} {n} (xs ys : Vec A n) → Comparison LessVec xs ys
  compareVec [] [] = equal refl
  compareVec (x ∷ xs) (y  ∷  ys) with compare x y
  compareVec (x ∷ xs) (y  ∷  ys) | less    x<y  = less    (head< x<y)
  compareVec (x ∷ xs) (y  ∷  ys) | greater y<x  = greater (head< y<x)
  compareVec (x ∷ xs) (.x ∷  ys) | equal   refl with compareVec xs ys
  compareVec (x ∷ xs) (.x ∷  ys) | equal   refl | less    xs<ys = less (tail< xs<ys)
  compareVec (x ∷ xs) (.x ∷  ys) | equal   refl | greater ys<xs = greater (tail< ys<xs)
  compareVec (x ∷ xs) (.x ∷ .xs) | equal   refl | equal   refl  = equal refl

instance
  OrdVec : ∀ {a} {A : Set a} {{OrdA : Ord A}} {n} → Ord (Vec A n)
  OrdVec = defaultOrd compareVec

--- Functor instances ---

instance
  ApplicativeVec : ∀ {a n} → Applicative {a} (flip Vec n)
  ApplicativeVec = record { pure = vec ; _<*>_ = vapp }

  FunctorVec : ∀ {a n} → Functor {a} (flip Vec n)
  FunctorVec = defaultApplicativeFunctor
