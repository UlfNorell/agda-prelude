
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

  vmap : ∀ {a b} {A : Set a} {B : Set b} {n} → (A → B) → Vec A n → Vec B n
  vmap f []       = []
  vmap f (x ∷ xs) = f x ∷ vmap f xs

vecToList : ∀ {a} {A : Set a} ..{n} → Vec A n → List A
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

vfoldr : ∀ {a b} {A : Set a} {B : Nat → Set b} → (∀ ..{n} → A → B n → B (suc n)) → B 0 → ∀ ..{n} → Vec A n → B n
vfoldr f z [] = z
vfoldr f z (x ∷ xs) = f x (vfoldr (λ {n} → f {n}) z xs)

vfoldl : ∀ {a b} {A : Set a} {B : Nat → Set b} → (∀ {n} → B n → A → B (suc n)) → B 0 → ∀ ..{n} → Vec A n → B n
vfoldl         f z [] = z
vfoldl {B = B} f z (x ∷ xs) = vfoldl {B = B ∘ suc} f (f z x) xs

--- Other list functions ---

module _ {a} {A : Set a} where

  infixr 5 _v++_
  _v++_ : ∀ {m n} → Vec A m → Vec A n → Vec A (m + n)
  []       v++ ys = ys
  (x ∷ xs) v++ ys = x ∷ xs v++ ys

  vreverse : ∀ ..{n} → Vec A n → Vec A n
  vreverse xs = vfoldl {B = Vec A} (flip _∷_) [] xs

--- Equality ---

vcons-inj-head : ∀ {a} {A : Set a} {x y : A} {n}
                   {xs ys : Vec A n} → x Vec.∷ xs ≡ y ∷ ys → x ≡ y
vcons-inj-head refl = refl

vcons-inj-tail : ∀ {a} {A : Set a} {x y : A} {n}
                   {xs ys : Vec A n} → x Vec.∷ xs ≡ y ∷ ys → xs ≡ ys
vcons-inj-tail refl = refl

instance
  EqVec : ∀ {a} {A : Set a} {{EqA : Eq A}} {n} → Eq (Vec A n)
  _==_ {{EqVec}} [] []             = yes refl
  _==_ {{EqVec}} (x ∷ xs) (y ∷ ys) with x == y
  ... | no neq   = no λ eq → neq (vcons-inj-head eq)
  ... | yes eq with xs == ys
  ...   | no neq  = no λ eq₁ → neq (vcons-inj-tail eq₁)
  ...   | yes eq₁ = yes (_∷_ $≡ eq *≡ eq₁)

--- Ord ---

data LessVec {a} {A : Set a} {{OrdA : Ord A}} : ∀ {n} → Vec A n → Vec A n → Set a where
  head< : ∀ ..{x y n} ..{xs ys : Vec A n} → x < y → LessVec (x ∷ xs) (y ∷ ys)
  tail< : ∀ ..{x n} ..{xs ys : Vec A n}   → LessVec xs ys → LessVec (x ∷ xs) (x ∷ ys)

private
  compareVec : ∀ {a} {A : Set a} {{OrdA : Ord A}} ..{n} (xs ys : Vec A n) → Comparison LessVec xs ys
  compareVec [] [] = equal refl
  compareVec (x ∷ xs) (y  ∷  ys) with compare x y
  compareVec (x ∷ xs) (y  ∷  ys) | less    x<y  = less    (head< x<y)
  compareVec (x ∷ xs) (y  ∷  ys) | greater y<x  = greater (head< y<x)
  compareVec (x ∷ xs) (.x ∷  ys) | equal   refl with compareVec xs ys
  compareVec (x ∷ xs) (.x ∷  ys) | equal   refl | less    xs<ys = less (tail< xs<ys)
  compareVec (x ∷ xs) (.x ∷  ys) | equal   refl | greater ys<xs = greater (tail< ys<xs)
  compareVec (x ∷ xs) (.x ∷ .xs) | equal   refl | equal   refl  = equal refl

private
  len : ∀ {a} {A : Set a} {n} → Vec A n → Nat
  len {n = n} _ = n

instance
  OrdVec : ∀ {a} {A : Set a} {{OrdA : Ord A}} {n} → Ord (Vec A n)
  OrdVec = defaultOrd compareVec

  OrdLawsVec : ∀ {a} {A : Set a} {{OrdA : Ord/Laws A}} {n} → Ord/Laws (Vec A n)
  Ord/Laws.super OrdLawsVec = it
  less-antirefl {{OrdLawsVec}} {[]} ()
  less-antirefl {{OrdLawsVec {A = A}}} {x ∷ xs} (head< lt) = less-antirefl {A = A} lt
  less-antirefl {{OrdLawsVec {A = A}}} {x ∷ xs} (tail< lt) = less-antirefl {A = Vec A (len xs)} {xs} lt
  less-trans {{OrdLawsVec {A = A}}} {[]} {[]} () _
  less-trans {{OrdLawsVec {A = A}}} {x ∷ xs} {y ∷ ys} {z ∷ zs} (head< lt) (head< lt₁) = head< (less-trans {A = A} lt lt₁)
  less-trans {{OrdLawsVec {A = A}}} {x ∷ xs} {y ∷ ys} {y ∷ zs} (head< lt) (tail< lt₁) = head< lt
  less-trans {{OrdLawsVec {A = A}}} {x ∷ xs} {x ∷ ys} {z ∷ zs} (tail< lt) (head< lt₁) = head< lt₁
  less-trans {{OrdLawsVec {A = A}}} {x ∷ xs} {x ∷ ys} {x ∷ zs} (tail< lt) (tail< lt₁) = tail< (less-trans {A = Vec A (len xs)} lt lt₁)

--- Functor instances ---

instance
  FunctorVec : ∀ {a n} → Functor {a} (flip Vec n)
  fmap {{FunctorVec}} = vmap

  FunctorVec′ : ∀ {a b n} → Functor′ {a} {b} (flip Vec n)
  fmap′ {{FunctorVec′}} = vmap

  ApplicativeVec : ∀ {a n} → Applicative {a} (flip Vec n)
  pure  {{ApplicativeVec}} = vec
  _<*>_ {{ApplicativeVec}} = vapp

  ApplicativeVec′ : ∀ {a b n} → Applicative′ {a} {b} (flip Vec n)
  _<*>′_ {{ApplicativeVec′}} = vapp
