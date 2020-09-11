module Container.List.All where

open import Prelude.Equality
open import Prelude.Nat
open import Prelude.Empty
open import Prelude.Unit
open import Prelude.Product
open import Prelude.Number
open import Prelude.List.Base

open import Prelude.Applicative

open import Agda.Primitive


infixr 5 _∷_
data All {a b} {A : Set a} (P : A → Set b) : List A → Set (a ⊔ b) where
  []  : All P []
  _∷_ : ∀ {x xs} (p : P x) (ps : All P xs) → All P (x ∷ xs)


module _ {a b} {A : Set a} {P Q : A → Set b} (f : ∀ {x} → P x → Q x) where
  mapAll : ∀ {xs} → All P xs → All Q xs
  mapAll [] = []
  mapAll (x ∷ xs) = f x ∷ mapAll xs


traverseAll : ∀ {a b} {A : Set a} {B : A → Set a} {F : Set a → Set b}
                {{AppF : Applicative F}} →
                (∀ x → F (B x)) → (xs : List A) → F (All B xs)
traverseAll f []       = pure []
traverseAll f (x ∷ xs) = ⦇ f x ∷ traverseAll f xs ⦈


module _ {a b} {A : Set a} {P : A → Set b} where

  -- Append

  infixr 5 _++All_
  _++All_ : ∀ {xs ys} → All P xs → All P ys → All P (xs ++ ys)
  []       ++All qs = qs
  (p ∷ ps) ++All qs = p ∷ ps ++All qs
