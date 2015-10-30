
module Tactic.Nat.Auto.Lemmas where

open import Prelude
open import Tactic.Nat.NF
open import Tactic.Nat.Exp
open import Data.Bag
open import Data.Nat.Properties.Core

map++ : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) (xs ys : List A) →
          map f (xs ++ ys) ≡ map f xs ++ map f ys
map++ f [] ys = refl
map++ f (x ∷ xs) ys rewrite map++ f xs ys = refl

prod++ : (xs ys : List Nat) → product (xs ++ ys) ≡ product xs * product ys
prod++ [] ys = refl
prod++ (x ∷ xs) ys rewrite prod++ xs ys = mul-assoc x _ _

private
  shuffle₁ : ∀ a b c d → a + ((b + c) + d) ≡ b + c + (a + d)
  shuffle₁ a b c d rewrite add-assoc a (b + c) d
                         | add-commute a (b + c)
                         | add-assoc (b + c) a d
                         = refl

  shuffle₂ : ∀ a b c d → a + b + (c + d) ≡ a + c + (b + d)
  shuffle₂ a b c d rewrite add-assoc (a + b) c d
                         | sym (add-assoc a b c)
                         | add-commute b c
                         | add-assoc a c b
                         | add-assoc (a + c) b d
                         = refl

  shuffle₃ : ∀ a b c d → (a * b) * (c * d) ≡ (a * c) * (b * d)
  shuffle₃ a b c d rewrite mul-assoc (a * b) c d
                         | sym (mul-assoc a b c)
                         | mul-commute b c
                         | mul-assoc a c b
                         | mul-assoc (a * c) b d = refl

  shuffle₄ : ∀ a b c d → a * (b * c * d) ≡ b * c * (a * d)
  shuffle₄ a b c d rewrite mul-assoc a (b * c) d
                         | mul-commute a (b * c)
                         | mul-assoc (b * c) a d
                         = refl

module _ {Atom : Set} {{_ : Ord Atom}} where
  ⟨+⟩-sound : ∀ v₁ v₂ (ρ : Env Atom) → ⟦ v₁ +nf v₂ ⟧n ρ ≡ ⟦ v₁ ⟧n ρ + ⟦ v₂ ⟧n ρ
  ⟨+⟩-sound [] []               ρ = refl
  ⟨+⟩-sound [] (_ ∷ _)          ρ = refl
  ⟨+⟩-sound (t ∷ v₁)  []        ρ = sym (add-0-r _)
  ⟨+⟩-sound ((i , t₁) ∷ v₁) ((j , t₂) ∷ v₂) ρ with compare t₁ t₂
  ... | less _ rewrite ⟨+⟩-sound v₁ ((j , t₂) ∷ v₂) ρ
                     = add-assoc (i * product (map ρ t₁)) _ _
  ... | equal eq rewrite eq | ⟨+⟩-sound v₁ v₂ ρ
                       | mul-distr-r i j (product (map ρ t₂))
                       = shuffle₂ (⟦ i , t₂ ⟧t ρ) (⟦ j , t₂ ⟧t ρ) _ _
  ... | greater _ rewrite ⟨+⟩-sound ((i , t₁) ∷ v₁) v₂ ρ
                        = shuffle₁ (⟦ j , t₂ ⟧t ρ) (⟦ i , t₁ ⟧t ρ) _ _

  map-merge : ∀ x y (ρ : Env Atom) → product (map ρ (merge x y)) ≡ product (map ρ x) * product (map ρ y)
  map-merge [] [] ρ = refl
  map-merge [] (x ∷ xs) ρ = refl
  map-merge (x ∷ xs) [] ρ = sym (mul-1-r _)
  map-merge (x ∷ xs) (y ∷ ys) ρ with x <? y
  ... | true  rewrite map-merge xs (y ∷ ys) ρ = mul-assoc (ρ x) _ _
  ... | false rewrite map-merge (x ∷ xs) ys ρ = shuffle₄ (ρ y) (ρ x) _ _

  mulTm-sound : ∀ t t′ (ρ : Env Atom) →
                  ⟦ mulTm t t′ ⟧t ρ ≡ ⟦ t ⟧t ρ * ⟦ t′ ⟧t ρ
  mulTm-sound (a , x) (b , y) ρ rewrite map-merge x y ρ
                                        = shuffle₃ a b _ _

  mulTmDistr : ∀ t v (ρ : Env Atom) → ⟦ map (mulTm t) v ⟧n ρ ≡ ⟦ t ⟧t ρ * ⟦ v ⟧n ρ
  mulTmDistr t [] ρ = sym (mul-0-r (⟦ t ⟧t ρ))
  mulTmDistr t (t′ ∷ v) ρ =
    ⟦ mulTm t t′ ⟧t ρ + ⟦ map (mulTm t) v ⟧n ρ
      ≡⟨ cong₂ _+_ (mulTm-sound t t′ ρ) (mulTmDistr t v ρ) ⟩
    ⟦ t ⟧t ρ * ⟦ t′ ⟧t ρ + ⟦ t ⟧t ρ * ⟦ v ⟧n ρ
      ≡⟨ mul-distr-l (⟦ t ⟧t ρ) _ _ ⟩ʳ
    ⟦ t ⟧t ρ * ⟦ t′ ∷ v ⟧n ρ ∎

  sort-sound : ∀ xs ρ → ⟦ nf-sort xs ⟧n ρ ≡ ⟦ xs ⟧n ρ
  sort-sound [] ρ = refl
  sort-sound (x ∷ xs) ρ rewrite ⟨+⟩-sound [ x ] (nf-sort xs) ρ
                              | sort-sound xs ρ
                              | add-0-r (⟦ x ⟧t ρ) = refl

  ⟨*⟩-sound : ∀ v₁ v₂ (ρ : Env Atom) → ⟦ v₁ *nf v₂ ⟧n ρ ≡ ⟦ v₁ ⟧n ρ * ⟦ v₂ ⟧n ρ
  ⟨*⟩-sound [] v₂ ρ = refl
  ⟨*⟩-sound (t ∷ v₁) v₂ ρ =
    ⟦ nf-sort (map (mulTm t) v₂) +nf (v₁ *nf v₂) ⟧n ρ
      ≡⟨ ⟨+⟩-sound (nf-sort (map (mulTm t) v₂)) (v₁ *nf v₂) ρ ⟩
    ⟦ nf-sort (map (mulTm t) v₂) ⟧n ρ + ⟦ v₁ *nf v₂ ⟧n ρ
      ≡⟨ cong (flip _+_ (⟦ v₁ *nf v₂ ⟧n ρ)) (sort-sound (map (mulTm t) v₂) ρ) ⟩
    ⟦ map (mulTm t) v₂ ⟧n ρ + ⟦ v₁ *nf v₂ ⟧n ρ
      ≡⟨ cong (_+_ (⟦ map (mulTm t) v₂ ⟧n ρ)) (⟨*⟩-sound v₁ v₂ ρ) ⟩
    ⟦ map (mulTm t) v₂ ⟧n ρ + ⟦ v₁ ⟧n ρ * ⟦ v₂ ⟧n ρ
      ≡⟨ cong (flip _+_ (⟦ v₁ ⟧n ρ * ⟦ v₂ ⟧n ρ)) (mulTmDistr t v₂ ρ) ⟩
    ⟦ t ⟧t ρ * ⟦ v₂ ⟧n ρ + ⟦ v₁ ⟧n ρ * ⟦ v₂ ⟧n ρ
      ≡⟨ mul-distr-r (⟦ t ⟧t ρ) _ _ ⟩ʳ
    ⟦ t ∷ v₁ ⟧n ρ * ⟦ v₂ ⟧n ρ ∎

  sound : ∀ e (ρ : Env Atom) → ⟦ e ⟧e ρ ≡ ⟦ norm e ⟧n ρ
  sound (var x) ρ =
    ρ x     ≡⟨ mul-1-r (ρ x) ⟩ʳ
    ρ x * 1 ≡⟨ add-0-r (ρ x * 1) ⟩ʳ
    (ρ x * 1) + 0 ∎
  sound (lit 0) ρ = refl
  sound (lit (suc n)) ρ rewrite mul-1-r n
                              | add-commute n 1
                              = sym (add-0-r _)
  sound (e ⟨+⟩ e₁) ρ =
    ⟦ e ⟧e ρ + ⟦ e₁ ⟧e ρ
      ≡⟨ cong₂ _+_ (sound e ρ) (sound e₁ ρ) ⟩
    ⟦ norm e ⟧n ρ + ⟦ norm e₁ ⟧n ρ
      ≡⟨ ⟨+⟩-sound (norm e) (norm e₁) ρ ⟩ʳ
    ⟦ norm e +nf norm e₁ ⟧n ρ ∎
  sound (e ⟨*⟩ e₁) ρ =
    ⟦ e ⟧e ρ * ⟦ e₁ ⟧e ρ
      ≡⟨ cong₂ _*_ (sound e ρ) (sound e₁ ρ) ⟩
    ⟦ norm e ⟧n ρ * ⟦ norm e₁ ⟧n ρ
      ≡⟨ ⟨*⟩-sound (norm e) (norm e₁) ρ ⟩ʳ
    ⟦ norm e *nf norm e₁ ⟧n ρ ∎

  module _ (ρ₁ ρ₂ : Env Atom) (eq : ∀ x → ρ₁ x ≡ ρ₂ x) where
    private
      lem-eval-env-a : ∀ a → product (map ρ₁ a) ≡ product (map ρ₂ a)
      lem-eval-env-a []       = refl
      lem-eval-env-a (x ∷ xs) = _*_ $≡ eq x *≡ lem-eval-env-a xs

      lem-eval-env-t : ∀ t → ⟦ t ⟧t ρ₁ ≡ ⟦ t ⟧t ρ₂
      lem-eval-env-t (k , a) = _*_ k $≡ lem-eval-env-a a

    lem-eval-env : ∀ n → ⟦ n ⟧n ρ₁ ≡ ⟦ n ⟧n ρ₂
    lem-eval-env [] = refl
    lem-eval-env (x ∷ n) = _+_ $≡ lem-eval-env-t x *≡ lem-eval-env n
