
module Data.List where

open import Prelude

infixr 5 _∷_
data All {a b} {A : Set a} (P : A → Set b) : List A → Set (a ⊔ b) where
  []  : All P []
  _∷_ : ∀ {x xs} (p : P x) (ps : All P xs) → All P (x ∷ xs)

data Any {a b} {A : Set a} (P : A → Set b) : List A → Set (a ⊔ b) where
  zero : ∀ {x xs} (p : P x) → Any P (x ∷ xs)
  suc  : ∀ {x xs} (i : Any P xs) → Any P (x ∷ xs)

pattern zero! = zero refl

-- Allows indices to be computed by instance search.
instance
  inst-Any-zero : ∀ {a b} {A : Set a} {P : A → Set b} {xs : List A} {x} {{p : P x}} → Any P (x ∷ xs)
  inst-Any-zero {{p}} = zero p

  inst-Any-suc : ∀ {a b} {A : Set a} {P : A → Set b} {xs : List A} {x} {{i : Any P xs}} → Any P (x ∷ xs)
  inst-Any-suc {{i}} = suc i

_∈_ : ∀ {a} {A : Set a} → A → List A → Set a
x ∈ xs = Any (_≡_ x) xs

forgetAny : ∀ {a p} {A : Set a} {P : A → Set p} {xs : List A} → Any P xs → Nat
forgetAny (zero _) = zero
forgetAny (suc  i) = suc (forgetAny i)

lookupAny : ∀ {a b} {A : Set a} {P Q : A → Set b} {xs} → All P xs → Any Q xs → Σ A (λ x → P x × Q x)
lookupAny (p ∷ ps) (zero q) = _ , p , q
lookupAny (p ∷ ps) (suc  i) = lookupAny ps i

lookup∈ : ∀ {a b} {A : Set a} {P : A → Set b} {xs x} → All P xs → x ∈ xs → P x
lookup∈ (p ∷ ps) (zero refl) = p
lookup∈ (p ∷ ps) (suc i)     = lookup∈ ps i

map∈ : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) {x xs} → x ∈ xs → f x ∈ map f xs
map∈ f (zero refl) = zero refl
map∈ f (suc i)     = suc (map∈ f i)
