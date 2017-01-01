
module Prelude.List where

open import Prelude.Nat
open import Prelude.Bool
open import Prelude.Maybe
open import Prelude.Product
open import Prelude.Empty
open import Prelude.Function
open import Prelude.Functor
open import Prelude.Applicative
open import Prelude.Monad
open import Prelude.Decidable
open import Prelude.Equality
open import Prelude.Ord
open import Prelude.Semiring
open import Prelude.Strict

open import Agda.Builtin.List public

infixr 5 _++_

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

foldl! : ∀ {a b} {A : Set a} {B : Set b} → (B → A → B) → B → List A → B
foldl! f z []       = z
foldl! f z (x ∷ xs) = force (f z x) λ z′ → foldl! f z′ xs

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

catMaybes : ∀ {a} {A : Set a} → List (Maybe A) → List A
catMaybes [] = []
catMaybes (x ∷ xs) = maybe (catMaybes xs) (_∷ catMaybes xs) x

all? : ∀ {a} {A : Set a} → (A → Bool) → List A → Bool
all? p []       = true
all? p (x ∷ xs) = p x && all? p xs

any? : ∀ {a} {A : Set a} → (A → Bool) → List A → Bool
any? p []       = true
any? p (x ∷ xs) = p x || any? p xs

take : ∀ {a} {A : Set a} → Nat → List A → List A
take zero    _        = []
take (suc n) []       = []
take (suc n) (x ∷ xs) = x ∷ take n xs

drop : ∀ {a} {A : Set a} → Nat → List A → List A
drop zero    xs       = xs
drop (suc n) []       = []
drop (suc n) (x ∷ xs) = drop n xs

splitAt : ∀ {a} {A : Set a} → Nat → List A → List A × List A
splitAt zero    xs       = [] , xs
splitAt (suc n) []       = [] , []
splitAt (suc n) (x ∷ xs) = first (x ∷_) (splitAt n xs)

null : ∀ {a} {A : Set a} → List A → Bool
null []      = true
null (_ ∷ _) = false

elem : ∀ {a} {A : Set a} {{EqA : Eq A}} → A → List A → Bool
elem x xs = not (null (filter (isYes ∘ _==_ x) xs))

lookup : ∀ {a b} {A : Set a} {B : Set b} {{EqA : Eq A}} → List (A × B) → A → Maybe B
lookup [] _ = nothing
lookup ((x₁ , v) ∷ xs) x = ifYes (x == x₁) then just v else lookup xs x

index : ∀ {a} {A : Set a} → List A → Nat → Maybe A
index [] _             = nothing
index (x ∷ xs) 0       = just x
index (x ∷ xs) (suc i) = index xs i

replicate : ∀ {a} {A : Set a} → Nat → A → List A
replicate zero x = []
replicate (suc n) x = x ∷ replicate n x

zipWith : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
            (A → B → C) → List A → List B → List C
zipWith f [] _ = []
zipWith f _ [] = []
zipWith f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith f xs ys

zip : ∀ {a b} {A : Set a} {B : Set b} → List A → List B → List (A × B)
zip = zipWith _,_

module _ {a b} {F : Set a → Set b} {{_ : Applicative F}} {A : Set a} where

  replicateA : Nat → F A → F (List A)
  replicateA zero    _ = pure []
  replicateA (suc n) x = pure _∷_ <*> x <*> replicateA n x

module _ {a} {A : Set a} {{_ : Semiring A}} where
  sum : List A → A
  sum = foldr _+_ zro

  product : List A → A
  product = foldr _*_ one

module _ {a} {A : Set a} {{_ : Ord A}} where
  insert : A → List A → List A
  insert x [] = x ∷ []
  insert x (y ∷ xs) = if x <? y then x ∷ y ∷ xs else y ∷ insert x xs

  sort : List A → List A
  sort [] = []
  sort (x ∷ xs) = insert x (sort xs)

infix 10 from_for_ from_to_ from_for_step_ from-to-step
from_for_ : Nat → Nat → List Nat
from 0 for 0     = []  -- make strict
from a for 0     = []
from a for suc d = a ∷ from suc a for d

from_for_step_ : Nat → Nat → Nat → List Nat
from 0 for 0     step _  = []  -- make strict
from a for 0     step _  = []
from a for suc c step d = a ∷ from a + d for c step d

from_to_ : Nat → Nat → List Nat
from a to b = from a for (suc b - a)

syntax from-to-step d a b = from a to b step d
from-to-step : (d : Nat) {{_ : NonZero d}} → Nat → Nat → List Nat
from-to-step d a b = from a for 1 + (b - a) div d step d

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

instance
  EqList : ∀ {a} {A : Set a} {{EqA : Eq A}} → Eq (List A)
  EqList = record { _==_ = eqList }

--- Ord ---

data LessList {a} {A : Set a} (_<_ : A → A → Set a) : List A → List A → Set a where
  nil<cons : ∀ {x xs} → LessList _<_ [] (x ∷ xs)
  head<    : ∀ {x y xs ys} → x < y → LessList _<_ (x ∷ xs) (y ∷ ys)
  tail<    : ∀ {x xs ys} → LessList _<_ xs ys → LessList _<_ (x ∷ xs) (x ∷ ys)

compareCons : ∀ {a} {A : Set a} {_<_ : A → A → Set a}
                {x : A} {xs : List A} {y : A} {ys : List A} →
                Comparison _<_ x y →
                Comparison (LessList _<_) xs ys →
                Comparison (LessList _<_) (x ∷ xs) (y ∷ ys)
compareCons (less lt)    _            = less (head< lt)
compareCons (greater gt) _            = greater (head< gt)
compareCons (equal refl) (less lt)    = less (tail< lt)
compareCons (equal refl) (greater gt) = greater (tail< gt)
compareCons (equal refl) (equal refl) = equal refl

compareList : ∀ {a} {A : Set a} {_<_ : A → A → Set a} (cmp : ∀ x y → Comparison _<_ x y) (xs ys : List A) →
              Comparison (LessList _<_) xs ys
compareList cmp [] [] = equal refl
compareList cmp [] (x ∷ ys) = less nil<cons
compareList cmp (x ∷ xs) [] = greater nil<cons
compareList cmp (x ∷ xs) (y ∷ ys) = compareCons (cmp x y) (compareList cmp xs ys)

instance
  OrdList : ∀ {a} {A : Set a} {{OrdA : Ord A}} → Ord (List A)
  OrdList = defaultOrd (compareList compare)

--- Functor ---

instance
  FunctorList : ∀ {a} → Functor (List {a})
  FunctorList = record { fmap = map }

  MonadList : ∀ {a} → Monad (List {a})
  MonadList = record { return = λ x → x ∷ [] ; _>>=_ = flip concatMap }

  MonadList′ : ∀ {a b} → Monad′ {a} {b} List
  MonadList′ = record { _>>=′_ = flip concatMap }

  ApplicativeList : ∀ {a} → Applicative (List {a})
  ApplicativeList = defaultMonadApplicative
