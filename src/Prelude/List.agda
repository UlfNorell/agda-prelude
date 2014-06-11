
module Prelude.List where

open import Prelude.Nat
open import Prelude.Bool
open import Prelude.Empty
open import Prelude.Function
open import Prelude.Functor
open import Prelude.Applicative
open import Prelude.Monad
open import Prelude.Decidable
open import Prelude.Equality
open import Prelude.Ord

infixr 5 _∷_ _++_
data List {a} (A : Set a) : Set a where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A

{-# BUILTIN LIST List #-}
{-# BUILTIN NIL  []   #-}
{-# BUILTIN CONS _∷_  #-}

{-# IMPORT Agda.FFI #-}
{-# COMPILED_DATA List Agda.FFI.AgdaList [] (:) #-}

pattern [_] x = x ∷ []

singleton : ∀ {a} {A : Set a} → A → List A
singleton x = x ∷ []

map : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

_++_ : ∀ {a} {A : Set a} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys

length : ∀ {a} {A : Set a} → List A → Nat
length []       = 0
length (x ∷ xs) = 1 + length xs

foldr : ∀ {a b} {A : Set a} {B : Set b} → (A → B → B) → B → List A → B
foldr f z []       = z
foldr f z (x ∷ xs) = f x (foldr f z xs)

foldl : ∀ {a b} {A : Set a} {B : Set b} → (B → A → B) → B → List A → B
foldl f z []       = z
foldl f z (x ∷ xs) = foldl f (f z x) xs

reverse : ∀ {a} {A : Set a} → List A → List A
reverse xs = foldl (flip _∷_) [] xs

concat : ∀ {a} {A : Set a} → List (List A) → List A
concat = foldr _++_ []

concatMap : ∀ {a b} {A : Set a} {B : Set b} → (A → List B) → List A → List B
concatMap f = concat ∘ map f

filter : ∀ {a} {A : Set a} → (A → Bool) → List A → List A
filter p [] = []
filter p (x ∷ xs) = if p x then x ∷ filter p xs
                           else filter p xs

null : ∀ {a} {A : Set a} → List A → Bool
null []      = true
null (_ ∷ _) = false

--- Equality ---

cons-inj-tail : ∀ {a} {A : Set a} {x : A} {xs : List A} {y : A}
               {ys : List A} →
             x ∷ xs ≡ y ∷ ys → xs ≡ ys
cons-inj-tail refl = refl

cons-inj-head : ∀ {a} {A : Set a} {x : A} {xs : List A} {y : A}
               {ys : List A} →
             x ∷ xs ≡ y ∷ ys → x ≡ y
cons-inj-head refl = refl

private
  dec-∷ : ∀ {a} {A : Set a} {x : A} {xs : List A} {y : A}
            {ys : List A} → Dec (x ≡ y) → Dec (xs ≡ ys) → Dec (x ∷ xs ≡ y ∷ ys)
  dec-∷ (yes refl) (yes refl) = yes refl
  dec-∷ _ (no neq) = no λ eq → neq (cons-inj-tail eq)
  dec-∷ (no neq) _ = no λ eq → neq (cons-inj-head eq)

  eqList : ∀ {a} {A : Set a} {{EqA : Eq A}} (xs ys : List A) → Dec (xs ≡ ys)
  eqList [] [] = yes refl
  eqList [] (_ ∷ _) = no (λ ())
  eqList (_ ∷ _) [] = no (λ ())
  eqList (x ∷ xs) (y ∷ ys) = dec-∷ (x == y) (eqList xs ys)

EqList : ∀ {a} {A : Set a} {{EqA : Eq A}} → Eq (List A)
EqList = record { _==_ = eqList }

--- Ord ---

data LessList {a} {A : Set a} {{OrdA : Ord A}} : List A → List A → Set a where
  nil<cons : ∀ {x xs} → LessList [] (x ∷ xs)
  head<    : ∀ {x y xs ys} → LessThan x y → LessList (x ∷ xs) (y ∷ ys)
  tail<    : ∀ {x xs ys} → LessList xs ys → LessList (x ∷ xs) (x ∷ ys)

private
  compareList : ∀ {a} {A : Set a} {{OrdA : Ord A}} (xs ys : List A) →
                Comparison LessList xs ys
  compareList [] [] = equal refl
  compareList [] (x ∷ ys) = less nil<cons
  compareList (x ∷ xs) [] = greater nil<cons
  compareList (x ∷ xs) (y ∷ ys) with compare x y
  compareList (x ∷ xs) (y ∷ ys)   | less x<y    = less (head< x<y)
  compareList (x ∷ xs) (y ∷ ys)   | greater x>y = greater (head< x>y)
  compareList (x ∷ xs) (.x ∷ ys)  | equal refl  with compareList xs ys
  compareList (x ∷ xs) (.x ∷ ys)  | equal refl | less xs<ys     = less (tail< xs<ys)
  compareList (x ∷ xs) (.x ∷ .xs) | equal refl | equal refl     = equal refl
  compareList (x ∷ xs) (.x ∷ ys)  | equal refl | greater xs>ys  = greater (tail< xs>ys)

OrdList : ∀ {a} {A : Set a} {{OrdA : Ord A}} → Ord (List A)
OrdList = record { LessThan = LessList ; compare = compareList }

--- Functor ---

FunctorList : ∀ {a} → Functor (List {a})
FunctorList = record { fmap = map }

MonadList : ∀ {a} → Monad (List {a})
MonadList = record { return = λ x → x ∷ [] ; _>>=_ = flip concatMap }

ApplicativeList : ∀ {a} → Applicative (List {a})
ApplicativeList = defaultMonadApplicative
