module Prelude.List.Base where

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
open import Prelude.Variables

open import Agda.Builtin.List public

infixr 5 _++_

pattern [_] x = x ∷ []

singleton : A → List A
singleton x = x ∷ []

map : (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

_++_ : List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys

length : List A → Nat
length []       = 0
length (x ∷ xs) = 1 + length xs

foldr : (A → B → B) → B → List A → B
foldr f z []       = z
foldr f z (x ∷ xs) = f x (foldr f z xs)

foldl : (B → A → B) → B → List A → B
foldl f z []       = z
foldl f z (x ∷ xs) = foldl f (f z x) xs

foldl! : (B → A → B) → B → List A → B
foldl! f z []       = z
foldl! f z (x ∷ xs) = force (f z x) λ z′ → foldl! f z′ xs

reverse : List A → List A
reverse xs = foldl (flip _∷_) [] xs

concat : List (List A) → List A
concat = foldr _++_ []

concatMap : (A → List B) → List A → List B
concatMap f = concat ∘ map f

filter : (A → Bool) → List A → List A
filter p [] = []
filter p (x ∷ xs) = if p x then x ∷ filter p xs
                           else filter p xs

catMaybes : List (Maybe A) → List A
catMaybes [] = []
catMaybes (x ∷ xs) = maybe (catMaybes xs) (_∷ catMaybes xs) x

all? : (A → Bool) → List A → Bool
all? p []       = true
all? p (x ∷ xs) = p x && all? p xs

any? : (A → Bool) → List A → Bool
any? p []       = false
any? p (x ∷ xs) = p x || any? p xs

take : Nat → List A → List A
take zero    _        = []
take (suc n) []       = []
take (suc n) (x ∷ xs) = x ∷ take n xs

drop : Nat → List A → List A
drop zero    xs       = xs
drop (suc n) []       = []
drop (suc n) (x ∷ xs) = drop n xs

takeWhile : (A → Bool) → List A → List A
takeWhile p []       = []
takeWhile p (x ∷ xs) = if p x then x ∷ takeWhile p xs
                              else []

dropWhile : (A → Bool) → List A → List A
dropWhile p [] = []
dropWhile p (x ∷ xs) = if p x then dropWhile p xs
                              else x ∷ xs

splitAt : Nat → List A → List A × List A
splitAt zero    xs       = [] , xs
splitAt (suc n) []       = [] , []
splitAt (suc n) (x ∷ xs) = first (x ∷_) (splitAt n xs)

null : List A → Bool
null []      = true
null (_ ∷ _) = false

elem : ⦃ Eq A ⦄ → A → List A → Bool
elem x xs = not (null (filter (isYes ∘ _==_ x) xs))

lookup : ⦃ Eq A ⦄ → List (A × B) → A → Maybe B
lookup [] _ = nothing
lookup ((x₁ , v) ∷ xs) x = ifYes (x == x₁) then just v else lookup xs x

nub : ⦃ Eq A ⦄ → List A → List A
nub [] = []
nub (x ∷ xs) = x ∷ filter (isNo ∘ (x ==_)) (nub xs)

index : List A → Nat → Maybe A
index [] _             = nothing
index (x ∷ xs) 0       = just x
index (x ∷ xs) (suc i) = index xs i

replicate : Nat → A → List A
replicate zero x = []
replicate (suc n) x = x ∷ replicate n x

zipWith : (A → B → C) → List A → List B → List C
zipWith f [] _ = []
zipWith f _ [] = []
zipWith f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith f xs ys

zip : List A → List B → List (A × B)
zip = zipWith _,_

punctuate : A → List A → List A
punctuate z []       = []
punctuate z [ x ]    = [ x ]
punctuate z (x ∷ xs) = x ∷ z ∷ punctuate z xs

replicateA : ⦃ Applicative F ⦄ → Nat → F A → F (List A)
replicateA zero    _ = pure []
replicateA (suc n) x = pure _∷_ <*> x <*> replicateA n x

module _ ⦃ _ : Semiring A ⦄ where

  sum : List A → A
  sum = foldl! _+_ zro

  product : List A → A
  product = foldl! _*_ one

  sumR : List A → A
  sumR = foldr _+_ zro

  productR : List A → A
  productR = foldr _*_ one

module _ ⦃ _ : Ord A ⦄ where

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

cons-inj-tail : x ∷ xs ≡ y ∷ ys → xs ≡ ys
cons-inj-tail refl = refl

cons-inj-head : x ∷ xs ≡ y ∷ ys → x ≡ y
cons-inj-head refl = refl

private
  dec-∷ : Dec (x ≡ y) → Dec (xs ≡ ys) → Dec (x ∷ xs ≡ y ∷ ys)
  dec-∷ (yes refl) (yes refl) = yes refl
  dec-∷ _ (no neq) = no λ eq → neq (cons-inj-tail eq)
  dec-∷ (no neq) _ = no λ eq → neq (cons-inj-head eq)

  eqList : ⦃ Eq A ⦄ → (xs ys : List A) → Dec (xs ≡ ys)
  eqList [] [] = yes refl
  eqList [] (_ ∷ _) = no (λ ())
  eqList (_ ∷ _) [] = no (λ ())
  eqList (x ∷ xs) (y ∷ ys) = dec-∷ (x == y) (eqList xs ys)

instance
  EqList : ⦃ Eq A ⦄ → Eq (List A)
  _==_ {{EqList}} = eqList

--- Ord ---

data LessList (_<_ : A → A → Set ℓ) : List A → List A → Set ℓ where
  nil<cons : LessList _<_ [] (x ∷ xs)
  head<    : x < y → LessList _<_ (x ∷ xs) (y ∷ ys)
  tail<    : LessList _<_ xs ys → LessList _<_ (x ∷ xs) (x ∷ ys)

compareCons : ∀ {_<_ : A → A → Set ℓ} →
                Comparison _<_ x y →
                Comparison (LessList _<_) xs ys →
                Comparison (LessList _<_) (x ∷ xs) (y ∷ ys)
compareCons (less lt)    _            = less (head< lt)
compareCons (greater gt) _            = greater (head< gt)
compareCons (equal refl) (less lt)    = less (tail< lt)
compareCons (equal refl) (greater gt) = greater (tail< gt)
compareCons (equal refl) (equal refl) = equal refl

compareList : ∀ {_<_ : A → A → Set ℓ} (cmp : ∀ x y → Comparison _<_ x y) (xs ys : List A) →
              Comparison (LessList _<_) xs ys
compareList cmp [] [] = equal refl
compareList cmp [] (x ∷ ys) = less nil<cons
compareList cmp (x ∷ xs) [] = greater nil<cons
compareList cmp (x ∷ xs) (y ∷ ys) = compareCons (cmp x y) (compareList cmp xs ys)

instance
  OrdList : ⦃ Ord A ⦄ → Ord (List A)
  OrdList = defaultOrd (compareList compare)

  OrdListLaws : ⦃ Ord/Laws A ⦄ → Ord/Laws (List A)
  Ord/Laws.super OrdListLaws = it
  less-antirefl {{OrdListLaws {A = A}}} (head< hd) = less-antirefl {A = A} hd
  less-antirefl {{OrdListLaws {A = A}}} (tail< tl) = less-antirefl {A = List A} tl
  less-trans {{OrdListLaws}} nil<cons   (head< hd)  = nil<cons
  less-trans {{OrdListLaws}} nil<cons   (tail< tl)  = nil<cons
  less-trans {{OrdListLaws {A = A}}} (head< hd) (head< hd₁) = head< (less-trans {A = A} hd hd₁)
  less-trans {{OrdListLaws {A = A}}} (head< hd) (tail< tl)  = head< hd
  less-trans {{OrdListLaws {A = A}}} (tail< tl) (head< hd)  = head< hd
  less-trans {{OrdListLaws {A = A}}} (tail< tl) (tail< tl₁) = tail< (less-trans {A = List A} tl tl₁)

--- Functor ---

instance
  FunctorList : Functor (List {ℓ})
  fmap {{FunctorList}} = map

  FunctorList′ : Functor′ {ℓ₁} {ℓ₂} List
  fmap′ {{FunctorList′}} = map

  ApplicativeList : Applicative (List {ℓ})
  pure  {{ApplicativeList}} x = x ∷ []
  _<*>_ {{ApplicativeList}} = monadAp (flip concatMap)

  ApplicativeList′ : Applicative′ {ℓ₁} {ℓ₂} List
  _<*>′_ {{ApplicativeList′}} = monadAp′ (flip concatMap)

  MonadList : Monad (List {ℓ})
  _>>=_  {{MonadList}} xs f = concatMap f xs

  MonadList′ : Monad′ {ℓ₁} {ℓ₂} List
  _>>=′_ {{MonadList′}} xs f = concatMap f xs

--- More functions ---

IsPrefixOf : {A : Set ℓ} → List A → List A → Set ℓ
IsPrefixOf xs ys = ∃ zs , ys ≡ xs ++ zs

isPrefixOf : ⦃ Eq A ⦄ → (xs ys : List A) → Dec (IsPrefixOf xs ys)
isPrefixOf []       ys = yes (ys , refl)
isPrefixOf (x ∷ xs) [] = no λ where (zs , ())
isPrefixOf (x ∷ xs) (y ∷ ys) with y == x | isPrefixOf xs ys
... | yes y=x | yes (zs , xs⊑ys) = yes (zs , (_∷_ $≡ y=x *≡ xs⊑ys))
... | _       | no noprefix      = no λ where (zs , eq) → noprefix ((zs , cons-inj-tail eq))
... | no  y≠x | _                = no λ where (zs , eq) → y≠x (cons-inj-head eq)

isPrefixOf? : ⦃ Eq A ⦄ → List A → List A → Bool
isPrefixOf? xs ys = isYes (isPrefixOf xs ys)

dropPrefix : ⦃ Eq A ⦄ → List A → List A → Maybe (List A)
dropPrefix xs ys =
  case isPrefixOf xs ys of λ where
    (yes (tl , _)) → just tl
    (no _)         → nothing

commonPrefix : ⦃ Eq A ⦄ → (xs ys : List A) → ∃ zs , IsPrefixOf zs xs × IsPrefixOf zs ys
commonPrefix [] ys = [] , (_ , refl) , (_ , refl)
commonPrefix xs [] = [] , (_ , refl) , (_ , refl)
commonPrefix (x ∷ xs) (y ∷ ys) with y == x | commonPrefix xs ys
... | yes y=x | zs , (xs₁ , eqx) , (ys₁ , eqy) = (x ∷ zs) , (xs₁ , (x ∷_ $≡ eqx)) , (ys₁ , (_∷_ $≡ y=x *≡ eqy))
... | no  _   | _                              = [] , (_ , refl) , (_ , refl)

commonPrefix! : ⦃ Eq A ⦄ → (xs ys : List A) → List A
commonPrefix! xs ys = fst (commonPrefix xs ys)

wordsBy : (A → Bool) → List A → List (List A)
wordsBy {A = A} p = go in-word ∘ dropWhile p
  where
    data Mode : Set where
      in-word in-space : Mode

    cons : A → List (List A) → List (List A)
    cons x []         = [ x ] ∷ []
    cons x (xs ∷ xss) = (x ∷ xs) ∷ xss

    go : Mode → List A → List (List A)
    go _    []       = []
    go mode     (x ∷ xs) with p x
    go mode     (x ∷ xs) | false = cons x (go in-word xs)
    go in-word  (x ∷ xs) | true  = [] ∷ go in-space xs
    go in-space (x ∷ xs) | true  = go in-space xs
