
module Container.List.Properties where

open import Prelude
open import Prelude.Nat.Properties

foldr-map-fusion : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
                     (f : B → C → C) (g : A → B) (z : C) (xs : List A) →
                     foldr f z (map g xs) ≡ foldr (f ∘ g) z xs
foldr-map-fusion f g z [] = refl
foldr-map-fusion f g z (x ∷ xs)
  rewrite foldr-map-fusion f g z xs
        = refl

foldl-map-fusion : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
                     (f : C → B → C) (g : A → B) (z : C) (xs : List A) →
                     foldl f z (map g xs) ≡ foldl (λ x y → f x (g y)) z xs
foldl-map-fusion f g z [] = refl
foldl-map-fusion f g z (x ∷ xs)
  rewrite foldl-map-fusion f g (f z (g x)) xs
        = refl

foldl-assoc : ∀ {a} {A : Set a} (f : A → A → A) →
                (∀ x y z → f x (f y z) ≡ f (f x y) z) →
                ∀ y z xs → foldl f (f y z) xs ≡ f y (foldl f z xs)
foldl-assoc f assoc y z [] = refl
foldl-assoc f assoc y z (x ∷ xs)
  rewrite sym (assoc y z x)
        = foldl-assoc f assoc y (f z x) xs

foldl-foldr : ∀ {a} {A : Set a} (f : A → A → A) (z : A) →
                (∀ x y z → f x (f y z) ≡ f (f x y) z) →
                (∀ x → f z x ≡ x) → (∀ x → f x z ≡ x) →
                ∀ xs → foldl f z xs ≡ foldr f z xs
foldl-foldr f z assoc idl idr [] = refl
foldl-foldr f z assoc idl idr (x ∷ xs)
  rewrite sym (foldl-foldr f z assoc idl idr xs)
        | idl x ⟨≡⟩ʳ idr x
        = foldl-assoc f assoc x z xs

foldl!-foldl : ∀ {a b} {A : Set a} {B : Set b} (f : B → A → B) z (xs : List A) →
                 foldl! f z xs ≡ foldl f z xs
foldl!-foldl f z [] = refl
foldl!-foldl f z (x ∷ xs) = forceLemma (f z x) (λ z′ → foldl! f z′ xs) ⟨≡⟩
                            foldl!-foldl f (f z x) xs

-- Properties of _++_

map-++ : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) (xs ys : List A) →
           map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++ f []       ys = refl
map-++ f (x ∷ xs) ys = f x ∷_ $≡ map-++ f xs ys

product-++ : (xs ys : List Nat) → productR (xs ++ ys) ≡ productR xs * productR ys
product-++ []       ys = sym (add-zero-r _)
product-++ (x ∷ xs) ys = x *_ $≡ product-++ xs ys ⟨≡⟩ mul-assoc x _ _
