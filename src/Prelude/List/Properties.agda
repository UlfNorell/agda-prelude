module Prelude.List.Properties where

open import Prelude.Function

open import Prelude.Bool
open import Prelude.Bool.Properties
open import Prelude.List.Base

open import Prelude.Decidable

open import Prelude.Monoid
open import Prelude.Semigroup

open import Prelude.Equality
open import Prelude.Equality.Inspect
open import Prelude.Variables

xs++[]≡[] : (xs : List A) → xs ++ [] ≡ xs
xs++[]≡[] [] = refl
xs++[]≡[] (x ∷ xs) = cong (x ∷_) (xs++[]≡[] xs)


xs++y∷ys≢[] :
  (xs : List A)
  → (y : A) → (ys : List A)
  → (xs ++ (y ∷ ys)) ≢ []
xs++y∷ys≢[] [] _ _ ()
xs++y∷ys≢[] (x ∷ xs) _ _ ()



map-map-fusion :
  (f : A → B) → (g : B → C)
  → (xs : List A)
  → map g (map f xs) ≡ map (g ∘ f) xs
map-map-fusion f g [] = refl
map-map-fusion f g (x ∷ xs) =
  cong ((g (f x)) ∷_) (map-map-fusion f g xs)


-- properties of ++

++-assoc : ∀ {ℓ} {A : Set ℓ} → (a b c : List A) → (a ++ b) ++ c ≡ a ++ b ++ c
++-assoc [] b c = refl
++-assoc (a ∷ as) b c =
  cong (a ∷_) (++-assoc as b c)

filter-++ :
    (f : A → Bool) → (l : List A) → (r : List A)
  → filter f (l ++ r) ≡ (filter f l ++ filter f r)
filter-++ f [] r = refl
filter-++ f (l ∷ ls) r
  with f l
...| true = cong (l ∷_) (filter-++ f ls r)
...| false = filter-++ f ls r

null-++ :
  ∀ {a} {A : Set a}
  → (l : List A) → (r : List A)
  → null (l ++ r) ≡ (null l && null r)
null-++ [] r = refl
null-++ (l ∷ xs) r =  refl

elem-++ :
  ⦃ EQA : Eq A ⦄
  → (x : A) → (l : List A) → (r : List A)
  → elem x (l ++ r) ≡ (elem x l || elem x r)
elem-++ x l r
  rewrite filter-++ (x ==?_) l r
  rewrite (null-++ (filter (x ==?_) l) (filter (x ==?_) r)) =
  de-morg-neg-conj (null (filter (x ==?_) l)) _

elem-filter :
  ⦃ _ : Eq A ⦄
  → (f : A → Bool)
  → (x : A)
  → (xs : List A)
  → elem x (filter f xs) ≡ true
  → f x ≡ true
elem-filter p x [] ()
elem-filter p x (x₁ ∷ xs) x∈res
  with inspect (p x₁) | (x == x₁)
... | false with≡ ¬p[x₁] | yes _ rewrite ¬p[x₁] = elem-filter p x xs x∈res
... | false with≡ ¬p[x₁] | no x≢x₁ rewrite ¬p[x₁] = elem-filter p x xs x∈res
... | true with≡ p[x₁] | yes x≡x₁ rewrite p[x₁] rewrite x≡x₁ = p[x₁]
... | true with≡ p[x₁] | no x≢x₁ rewrite p[x₁]
  with x == x₁
...| yes x₁≡x rewrite x₁≡x = p[x₁]
...| no x₁≢x = elem-filter p x xs x∈res


-- Monoid / Semigroup instance and lemmas

instance
  SemigroupLawsList : ∀ {ℓ} {A : Set ℓ} → Semigroup/Laws (List A)
  Semigroup/Laws.super SemigroupLawsList = it
  semigroup-assoc {{SemigroupLawsList}} = ++-assoc

  MonoidLawsList : ∀ {ℓ} {A : Set ℓ} → Monoid/Laws (List A)
  Monoid/Laws.super MonoidLawsList = it
  left-identity  ⦃ MonoidLawsList ⦄ _ = refl
  right-identity ⦃ MonoidLawsList ⦄   = xs++[]≡[]
  monoid-assoc ⦃ MonoidLawsList ⦄ = ++-assoc
