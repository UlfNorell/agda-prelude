module Prelude.List.Relations.Any where

open import Agda.Primitive

open import Prelude.Nat
open import Prelude.List.Base
open import Prelude.Equality

open import Prelude.List.Relations.All


data Any {a b} {A : Set a} (P : A → Set b) : List A → Set (a ⊔ b) where
  zero : ∀ {x xs} (p : P x) → Any P (x ∷ xs)
  suc  : ∀ {x xs} (i : Any P xs) → Any P (x ∷ xs)

pattern zero! = zero refl


infix 3 _∈_
_∈_ : ∀ {a} {A : Set a} → A → List A → Set a
x ∈ xs = Any (_≡_ x) xs


module _ {a b} {A : Set a} {P : A → Set b} where
  -- Delete

  deleteIx : ∀ xs → Any P xs → List A
  deleteIx (_ ∷ xs) (zero _) = xs
  deleteIx (x ∷ xs) (suc  i) = x ∷ deleteIx xs i

  deleteAllIx : ∀ {c} {Q : A → Set c} {xs} → All Q xs → (i : Any P xs) → All Q (deleteIx xs i)
  deleteAllIx (q ∷ qs) (zero _) = qs
  deleteAllIx (q ∷ qs) (suc i)  = q ∷ deleteAllIx qs i

forgetAny : ∀ {a p} {A : Set a} {P : A → Set p} {xs : List A} → Any P xs → Nat
forgetAny (zero _) = zero
forgetAny (suc  i) = suc (forgetAny i)
