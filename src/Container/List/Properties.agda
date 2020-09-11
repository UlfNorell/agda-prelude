module Container.List.Properties where

open import Prelude
open import Prelude.Nat.Properties
open import Prelude.Variables
open import Container.List


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

deleteIx-++-left :
  (x : A)
  → (xs ys : List A)
  → (x∈xs : x ∈ xs)
  → Σ (x ∈ (xs ++ ys))
      (λ x∈xs++ys →
        deleteIx xs x∈xs ++ ys ≡ deleteIx (xs ++ ys) x∈xs++ys)
deleteIx-++-left x (x₁ ∷ xs) ys (zero p) = zero p , refl
deleteIx-++-left x (x₁ ∷ xs) ys (suc x∈xs) =
  (suc (fst (deleteIx-++-left x xs ys x∈xs)))
  , cong (x₁ ∷_) (snd (deleteIx-++-left x xs ys x∈xs))

deleteIx-++-right :
  (y : A)
  → (xs ys : List A)
  → (y∈ys : y ∈ ys)
  → Σ (y ∈ (xs ++ ys))
      (λ y∈xs++ys →
         xs ++ deleteIx ys y∈ys ≡ deleteIx (xs ++ ys) y∈xs++ys)
deleteIx-++-right y [] ysy y∈ys = y∈ys , refl
deleteIx-++-right y (x ∷ xs) ysy y∈ys =
  (suc (fst (deleteIx-++-right y xs ysy y∈ys)))
  , cong (x ∷_) (snd (deleteIx-++-right y xs ysy y∈ys))

deleteIx-++-both :
  (x y : A)
  → (xs ys : List A)
  → (x∈xs : x ∈ xs) → (y∈ys : y ∈ ys)
  → Σ (y ∈ (xs ++ ys))
      (λ y∈xs++ys →
        Σ (x ∈ (deleteIx (xs ++ ys) y∈xs++ys))
          (λ x∈xs++ys →
             deleteIx xs x∈xs ++ deleteIx ys y∈ys ≡ deleteIx (deleteIx (xs ++ ys) y∈xs++ys) x∈xs++ys
          ))
deleteIx-++-both x y xs ys x∈xs y∈ys
  with deleteIx-++-left x xs (deleteIx ys y∈ys) x∈xs
...| x∈[xs++del[ys]]  , eq₁ rewrite eq₁
  with deleteIx-++-right y xs ys y∈ys
...| y∈del[xs++ys] , eq₂ rewrite eq₂ =
  y∈del[xs++ys] , (x∈[xs++del[ys]] , refl)



x∈del[xs]⇒x∈xs :
  {x y : A} → {xs : List A}
  → (y∈xs : y ∈ xs)
  → (x ∈ deleteIx xs y∈xs)
  → x ∈ xs
x∈del[xs]⇒x∈xs zero! zero! = suc zero!
x∈del[xs]⇒x∈xs zero! (suc x∈del[xs]) = suc (suc x∈del[xs])
x∈del[xs]⇒x∈xs (suc y∈xs) zero! = zero!
x∈del[xs]⇒x∈xs (suc y∈xs) (suc x∈del[xs]) =
  suc (x∈del[xs]⇒x∈xs y∈xs x∈del[xs])


deleteIx-comm :
  ∀ {x y : A} {xs : List A}
  → (x∈xs : x ∈ xs)
  → (y∈del[xs] : y ∈ deleteIx xs x∈xs)
  → Σ (y ∈ xs)
      (λ y∈xs →  Σ (x ∈ deleteIx xs y∈xs)
        (λ x∈del[xs] →
          deleteIx (deleteIx xs x∈xs) y∈del[xs]
          ≡ deleteIx (deleteIx xs y∈xs) x∈del[xs]))
deleteIx-comm zero! zero! = (suc zero!) , (zero! , refl)
deleteIx-comm zero! (suc y∈del[xs]) = (suc (suc y∈del[xs])) , (zero! , refl)
deleteIx-comm (suc x∈xs) zero! = zero! , x∈xs , refl
deleteIx-comm (suc x∈xs) (suc y∈del[xs])
  with (deleteIx-comm x∈xs y∈del[xs])
...| a , b , c = (suc a) , ((suc b) , cong (_ ∷_) c)

∈-++-right :
  {y : A}
  → (xs : List A)
  → {ys : List A}
  → y ∈ ys
  → y ∈ (xs ++ ys)
∈-++-right [] y∈ys = y∈ys
∈-++-right (x ∷ xs) y∈ys = suc (∈-++-right xs y∈ys)

∈-++-left :
  {x : A}
  → (xs ys : List A)
  → x ∈ xs
  → x ∈ (xs ++ ys)
∈-++-left [] ys ()
∈-++-left (x ∷ xs) ys (zero p) = zero p
∈-++-left (x ∷ xs) ys (suc x∈xs) = suc (∈-++-left xs ys x∈xs)

deleteIx-∈-++-left :
    (x : A)
  → (xs ys : List A)
  → (x∈xs : x ∈ xs)
  → deleteIx (xs ++ ys) (∈-++-left xs ys x∈xs)
    ≡ (deleteIx xs x∈xs) ++ ys
deleteIx-∈-++-left x (x₁ ∷ xs) ys (zero p) = refl
deleteIx-∈-++-left x (x₁ ∷ xs) ys (suc x∈xs) =
  cong (x₁ ∷_) (deleteIx-∈-++-left x xs ys x∈xs)

deleteIx-∈-++-right-head :
    (y : A)
  → (xs : List A)
  → (ys : List A)
  → deleteIx (xs ++ y ∷ ys) (∈-++-right xs zero!)
    ≡ (xs ++ ys)
deleteIx-∈-++-right-head _ [] ys = refl
deleteIx-∈-++-right-head _ (x ∷ xs) ys =
  cong (x ∷_) (deleteIx-∈-++-right-head _ xs ys)
