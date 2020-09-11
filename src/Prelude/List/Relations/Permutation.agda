module Prelude.List.Relations.Permutation where

open import Prelude.Equality using (_≡_ ; transport )
import Prelude.Equality as Eq
open import Prelude.Product
open import Prelude.Function

open import Prelude.Monoid
open import Prelude.List.Base
open import Prelude.List.Properties
open import Prelude.List.Relations.Any
open import Prelude.List.Relations.Properties
open import Prelude.Variables

data Permutation {a} {A : Set a} : List A → List A → Set a where
  []  : Permutation [] []
  _∷_ : ∀ {x xs ys} (i : x ∈ ys) → Permutation xs (deleteIx ys i) →
          Permutation (x ∷ xs) ys

null-perm : {xs : List A}
          → Permutation xs []
          → xs ≡ []
null-perm {xs = .[]} [] = Eq.refl

refl : (xs : List A)
     → Permutation xs xs
refl [] = []
refl (x ∷ xs) = zero! ∷ refl xs

from-≡ : {xs ys : List A}
        → xs ≡ ys
        → Permutation xs ys
from-≡ {xs = xs} {ys = .xs} Eq.refl = refl xs

swap-cons-right :
  {x x₁ : A} {xs ys : List A}
  → Permutation ys (x ∷ x₁ ∷ xs)
  → Permutation ys (x₁ ∷ x ∷ xs)
swap-cons-right (zero p ∷ perm) =
  suc (zero p) ∷ perm
swap-cons-right (suc zero! ∷ perm) =
  zero! ∷ perm
swap-cons-right (suc (suc i) ∷ perm) =
  suc (suc i) ∷ swap-cons-right perm

cons :
  (x : A) {xs ys : List A}
  → Permutation xs ys
  → Permutation (x ∷ xs) (x ∷ ys)
cons _ p = zero! ∷ p

right-head-in :
  {x : A} {xs ys : List A}
  → Permutation xs (x ∷ ys)
  → x ∈ xs
right-head-in (zero! ∷ p) = zero!
right-head-in (suc i ∷ p) = suc (right-head-in p)


move-deleteIx-left :
  {x : A} {xs ys : List A}
  → (p : Permutation xs (x ∷ ys))
  → Permutation (deleteIx xs (right-head-in p)) ys
move-deleteIx-left (zero! ∷ p) = p
move-deleteIx-left (suc i ∷ p) = i ∷ move-deleteIx-left p


deleteIx-destr-left :
  {x : A} {xs ys : List A}
  → (x∈xs : x ∈ xs)
  → Permutation (deleteIx xs x∈xs) ys
  → Permutation xs (x ∷ ys)
deleteIx-destr-left zero! [] = zero! ∷ []
deleteIx-destr-left zero! (i ∷ p₁) = zero! ∷ (i ∷ p₁)
deleteIx-destr-left (suc x∈xs) (i ∷ p) = (suc i) ∷ (deleteIx-destr-left x∈xs p)

deleteIx-destr-right :
  {y : A} {xs ys : List A}
  → (y∈ys : y ∈ ys)
  → Permutation xs (deleteIx ys y∈ys)
  → Permutation (y ∷ xs) ys
deleteIx-destr-right (zero p) [] = zero p ∷ []
deleteIx-destr-right (zero p) (i ∷ p₁) = zero p ∷ deleteIx-destr-right i p₁
deleteIx-destr-right (suc y∈ys) (i ∷ p) = (suc y∈ys) ∷ (i ∷ p)

deleteIx-destr :
  {x y : A} {xs ys : List A}
  → (x∈xs : x ∈ xs) → (y∈ys : y ∈ ys)
  → Permutation (deleteIx xs x∈xs) (deleteIx ys y∈ys)
  → Permutation (y ∷ xs) (x ∷ ys)
deleteIx-destr x∈xs y∈ys p =
  deleteIx-destr-right (suc y∈ys) (deleteIx-destr-left x∈xs p)


deleteIx-head-right :
  {x : A} {xs ys : List A}
  → Permutation xs (x ∷ ys)
  → Σ (x ∈ xs)
      (λ x∈xs → Permutation (deleteIx xs x∈xs) ys)
deleteIx-head-right (zero! ∷ p) = zero! , p
deleteIx-head-right (suc i ∷ p) =
  suc (fst (deleteIx-head-right p))
  , i ∷ snd (deleteIx-head-right p)

deleteIx-head-left :
  {x : A} {xs ys : List A}
  → Permutation (x ∷ xs) ys
  → Σ (x ∈ ys)
      (λ x∈ys → Permutation xs (deleteIx ys x∈ys))
deleteIx-head-left (zero! ∷ p) = zero! , p
deleteIx-head-left (suc i ∷ p) = (suc i) , p

deleteIx-tail-right :
  {x : A} {xs ys  : List A}
  → (x∈ys : x ∈ ys)
  → Permutation xs (x ∷ deleteIx ys x∈ys)
  → Permutation xs ys
deleteIx-tail-right x∈ys (zero! ∷ p) = x∈ys ∷ p
deleteIx-tail-right (zero p₁) (suc i ∷ p)
  rewrite p₁ = suc i ∷ p
deleteIx-tail-right (suc x∈ys) (suc (zero p₁) ∷ p) =
  zero p₁ ∷ deleteIx-tail-right x∈ys p
deleteIx-tail-right (suc x∈ys) (suc (suc x₂∈del[ys]) ∷ p)
  with deleteIx-comm x∈ys x₂∈del[ys]
...| y∈ys , x∈del[ys] , eq rewrite eq =
  (suc y∈ys) ∷ deleteIx-tail-right (suc x∈del[ys]) p

sym : {xs ys : List A}
    → Permutation xs ys
    → Permutation ys xs
sym {xs = []} {ys = []} [] = []
sym {xs = []} {ys = (x ∷ ys)} ()
sym {xs = (x ∷ xs)} {ys = .(_ ∷ _)} ((zero {x₁} {xs₁} x≡x₁) ∷ p)
  rewrite x≡x₁ =
  zero Eq.refl ∷ sym p
sym {xs = (x ∷ xs)} {ys = .(_ ∷ _)} (suc {x₁} {xs₁} i ∷ p)
  with sym p
... | i₁ ∷ per-xs₁-xs\i = deleteIx-destr i i₁ per-xs₁-xs\i

swap-cons-left :
  {x x₁ : A} {xs ys : List A}
  → Permutation (x ∷ x₁ ∷ xs) ys
  → Permutation (x₁ ∷ x ∷ xs) ys
swap-cons-left {_} {_} {x} {x₁} {xs} {ys} p
  with sym p
...| p' = sym (swap-cons-right p')

swap-cons :
    {x x₁ y y₁ : A} {xs ys : List A}
    → Permutation (x ∷ x₁ ∷ xs) (y ∷ y₁ ∷ ys)
    → Permutation (x₁ ∷ x ∷ xs) (y₁ ∷ y ∷ ys)
swap-cons = swap-cons-left ∘ swap-cons-right


trans :
  {xs ys zs : List A}
  → Permutation xs ys → Permutation ys zs
  → Permutation xs zs
trans [] [] = []
trans (zero! ∷ p-xs-ys) (zero! ∷ p-ys-zs) =
  zero! ∷ trans p-xs-ys p-ys-zs
trans (zero! ∷ p-xs-ys) (suc i₁ ∷ p-ys-zs) =
  suc i₁ ∷ trans p-xs-ys p-ys-zs
trans (suc i ∷ p-xs-ys) (p@zero! ∷ p-ys-zs) =
  let (x∈xs , p-xs-ys') = deleteIx-head-right p-xs-ys
      p-xs-ys'' = deleteIx-destr-right i p-xs-ys'
      (x∈ys , p-xs-zs')  = deleteIx-head-left (trans p-xs-ys'' p-ys-zs)
  in deleteIx-destr x∈xs x∈ys p-xs-zs'
trans (suc i ∷ p-xs-ys) (suc i₁ ∷ p-ys-zs) =
  let (x∈xs , p-xs-ys') = deleteIx-head-right p-xs-ys
      p-xs-ys'' = deleteIx-destr-right i p-xs-ys'
      (x∈ys , foo)  = deleteIx-head-left (trans p-xs-ys'' p-ys-zs)
  in deleteIx-tail-right (suc i₁) (deleteIx-destr x∈xs x∈ys foo)


cons-++ :
  (x : A) → (xs ys : List A)
  → Permutation (x ∷ xs ++ ys) (xs ++ x ∷ ys)
cons-++ _ [] ys = zero! ∷ refl ys
cons-++ x  (x₁ ∷ xs) ys =
  ∈-++-right (x₁ ∷ xs) zero!
  ∷ transport (λ z → Permutation (x₁ ∷ xs ++ ys) (x₁ ∷ z))
               (Eq.sym (deleteIx-∈-++-right-head x xs ys))
               (refl (x₁ ∷ xs ++ ys))

permuation-++ :
  {xs ys xs' ys' : List A}
  → Permutation xs xs'
  → Permutation ys ys'
  → Permutation (xs ++ ys) (xs' ++ ys')
permuation-++ [] [] = []
permuation-++ [] (i ∷ perm-ys-ys') = i ∷ perm-ys-ys'
permuation-++ {xs = xs} {xs' = xs'} (i ∷ perm-xs-xs') []
  rewrite right-identity xs' rewrite right-identity xs =
    i ∷ perm-xs-xs'
permuation-++ (zero {x} {xs'} Eq.refl ∷ perm-xs-xs') (zero {y} {ys'} Eq.refl ∷ perm-ys-ys') =
  zero! ∷ trans (sym (cons-++ y _ _))
                 (trans (cons y (permuation-++ perm-xs-xs' perm-ys-ys'))
                        (cons-++ y xs' ys'))
permuation-++ (_∷_ {x} {xs} {(_ ∷ xs')} (zero Eq.refl) perm-xs-xs')
              (_∷_ {y} {( y₁ ∷ ys)} {( y₁' ∷ ys')} (suc y∈ys') perm-ys-ys') =
  let (y∈xs₁++x₂∷xs₂ , perm') = deleteIx-++-right y xs' (y₁' ∷ ys') (suc y∈ys')
  in zero!
     ∷ trans (sym (cons-++ y xs (y₁ ∷ ys)))
              (deleteIx-tail-right
                y∈xs₁++x₂∷xs₂
                (cons y
                  (transport (λ z → Permutation (xs ++ y₁ ∷ ys) z)
                             perm'
                             (permuation-++ perm-xs-xs' perm-ys-ys'))))
permuation-++ (_∷_ {x} {(x₁ ∷ xs)} {(x₁' ∷ xs')} (suc x∈xs') perm-xs-xs')
              (_∷_ {y} {ys} {_ ∷ ys'} zero! perm-ys-ys') =
  ∈-++-left (x₁' ∷ xs') (y ∷ ys') (suc x∈xs')
  ∷ transport (λ z → Permutation (x₁ ∷ xs ++ y ∷ ys) (x₁' ∷ z))
               (Eq.sym (deleteIx-∈-++-left x xs' (y ∷ ys') x∈xs'))
               (trans (trans (sym (cons-++ y (x₁ ∷ xs) ys))
                       (cons y (permuation-++ perm-xs-xs' perm-ys-ys')))
                       (cons-++ y (x₁' ∷ _) ys'))
permuation-++ (_∷_ {x} {(x₁ ∷ xs)} {(x₁' ∷ xs')} (suc x∈xs') perm-xs-xs')
              (_∷_ {y} {( y₁ ∷ ys)} {( y₁' ∷ ys')} (suc y∈ys') perm-ys-ys')
  with deleteIx-++-right y (y ∷ x₁' ∷ deleteIx xs' x∈xs') (y₁' ∷ ys') (suc y∈ys')
... | zero! , foo =
  ∈-++-left (x₁' ∷ xs') (y₁' ∷ ys') (suc x∈xs')
  ∷  trans (transport (λ z → Permutation (x₁ ∷ xs ++ y ∷ y₁ ∷ ys) z)
                     foo
                     (trans (sym (cons-++ y (x₁ ∷ xs) (y₁ ∷ ys)))
                            (cons y (permuation-++ perm-xs-xs' perm-ys-ys'))))
           (zero! ∷ (from-≡ (Eq.sym (deleteIx-∈-++-left x xs' (y₁' ∷ ys') x∈xs'))))
... | suc y∈ , foo =
  ∈-++-left (x₁' ∷ xs') (y₁' ∷ ys') (suc x∈xs')
  ∷ trans (deleteIx-tail-right y∈
              (transport (λ z → Permutation (x₁ ∷ xs ++ y ∷ y₁ ∷ ys) z)
                                   foo
                                   (trans (sym (cons-++ y (x₁ ∷ xs) (y₁ ∷ ys)))
                                          (cons y (permuation-++ perm-xs-xs' perm-ys-ys'))))
              )
            (from-≡ (Eq.sym (deleteIx-∈-++-left x (x₁' ∷ xs') (y₁' ∷ ys') (suc  x∈xs'))))



flip-++-right :
  (ys zs : List A)
  → Permutation xs (ys ++ zs)
  → Permutation xs (zs ++ ys)
flip-++-right ys [] perm
  rewrite right-identity ys = perm
flip-++-right ys (z ∷ zs) perm =
  let (z∈ , swap) = deleteIx-head-right (trans perm (sym (cons-++ z ys zs)))
  in deleteIx-destr-left z∈ (flip-++-right ys zs swap)

flip-++-left :
  (xs ys : List A)
  → Permutation (xs ++ ys) zs
  → Permutation (ys ++ xs) zs
flip-++-left xs ys p = sym (flip-++-right xs ys (sym p))

flip-++ :
  (xs xs' ys ys' : List A)
  → Permutation (xs ++ xs') (ys ++ ys')
  → Permutation (xs' ++ xs) (ys' ++ ys)
flip-++ xs xs' ys ys' p =
  flip-++-left xs xs' (flip-++-right ys ys' p)
