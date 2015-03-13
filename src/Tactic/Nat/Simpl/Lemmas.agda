
module Tactic.Nat.Simpl.Lemmas where

open import Prelude
open import Tactic.Nat.NF
open import Tactic.Nat.Exp
open import Tactic.Nat.Bag
open import Tactic.Nat.Auto
open import Data.Nat.Properties
open import Data.List.Properties
open import Tactic.Nat.Auto.Lemmas

NFEqS : NF × NF → Env → Set
NFEqS (nf₁ , nf₂) ρ = ⟦ nf₁ ⟧ns ρ ≡ ⟦ nf₂ ⟧ns ρ

NFEq : NF × NF → Env → Set
NFEq (nf₁ , nf₂) ρ = ⟦ nf₁ ⟧n ρ ≡ ⟦ nf₂ ⟧n ρ

product1-sound : ∀ xs → product1 xs ≡ product xs
product1-sound [] = refl
product1-sound (x ∷ xs)
  rewrite sym (cong (λ x → foldl _*_ x xs) (mul-1-r x))
        | foldl-assoc _*_ mul-assoc x 1 xs
        | foldl-foldr _*_ 1 mul-assoc (λ _ → refl) mul-1-r xs
        = refl

ts-sound : ∀ x ρ → ⟦ x ⟧ts ρ ≡ ⟦ x ⟧t ρ
ts-sound (0 , x) ρ = mul-0-r (product1 (map ρ x))
ts-sound (1 , x) ρ = product1-sound (map ρ x)
ts-sound (suc (suc i) , x) ρ
  rewrite sym (product1-sound (map ρ x))
        = tactic auto

map-eq : ∀ {a b} {A : Set a} {B : Set b} (f g : A → B) →
           (∀ x → f x ≡ g x) → ∀ xs → map f xs ≡ map g xs
map-eq f g f=g [] = refl
map-eq f g f=g (x ∷ xs) rewrite f=g x | map-eq f g f=g xs = refl

private
  et  = flip ⟦_⟧t
  ets = flip ⟦_⟧ts

ns-sound : ∀ nf ρ → ⟦ nf ⟧ns ρ ≡ ⟦ nf ⟧n ρ
ns-sound [] ρ = refl
ns-sound (x ∷ nf) ρ
  rewrite sym (foldl-map-fusion _+_ (ets ρ) (ets ρ x) nf)
        | ts-sound x ρ
        | map-eq (ets ρ) (et ρ) (flip ts-sound ρ) nf
        | sym (foldl-foldr _+_ 0 add-assoc (λ _ → refl) add-0-r (map (et ρ) nf))
        | sym (foldl-assoc _+_ add-assoc (et ρ x) 0 (map (et ρ) nf))
        | add-0-r (et ρ x)
        = refl

fst-*** : ∀ {a b} {A₁ A₂ : Set a} {B₁ B₂ : Set b}
            (f : A₁ → B₁) (g : A₂ → B₂) (p : A₁ × A₂) →
            fst ((f *** g) p) ≡ f (fst p)
fst-*** f g (x , y) = refl

snd-*** : ∀ {a b} {A₁ A₂ : Set a} {B₁ B₂ : Set b}
            (f : A₁ → B₁) (g : A₂ → B₂) (p : A₁ × A₂) →
            snd ((f *** g) p) ≡ g (snd p)
snd-*** f g (x , y) = refl

eta : ∀ {a b} {A : Set a} {B : Set b} (p : A × B) → p ≡ (fst p , snd p)
eta (x , y) = refl

shuffle₁ : ∀ a b c → a + (b + c) ≡ b + (a + c)
shuffle₁ a b c = tactic auto

cancel-sound′ : ∀ a b nf₁ nf₂ ρ → a + ⟦ fst (cancel nf₁ nf₂) ⟧n ρ ≡ b + ⟦ snd (cancel nf₁ nf₂) ⟧n ρ →
                             a + ⟦ nf₁ ⟧n ρ ≡ b + ⟦ nf₂ ⟧n ρ
cancel-sound′ a b [] []        ρ H = H
cancel-sound′ a b [] (x ∷ nf₂) ρ H = H
cancel-sound′ a b (x ∷ nf₁) [] ρ H = H
cancel-sound′ a b ((i , x) ∷ nf₁) ((j , y) ∷ nf₂) ρ H
  with compare x y
... | less    _ rewrite fst-*** (List._∷_ (i , x)) id (cancel nf₁ ((j , y) ∷ nf₂))
                      | snd-*** (List._∷_ (i , x)) id (cancel nf₁ ((j , y) ∷ nf₂))
                      | add-assoc a (et ρ (i , x)) (⟦ fst (cancel nf₁ ((j , y) ∷ nf₂)) ⟧n ρ)
                      | add-assoc a (et ρ (i , x)) (⟦ nf₁ ⟧n ρ)
                      = cancel-sound′ (a + et ρ (i , x)) b nf₁ ((j , y) ∷ nf₂) ρ H
... | greater _ rewrite fst-*** id (List._∷_ (j , y)) (cancel ((i , x) ∷ nf₁) nf₂)
                      | snd-*** id (List._∷_ (j , y)) (cancel ((i , x) ∷ nf₁) nf₂)
                      | add-assoc b (et ρ (j , y)) (⟦ snd (cancel ((i , x) ∷ nf₁) nf₂) ⟧n ρ)
                      | add-assoc b (et ρ (j , y)) (⟦ nf₂ ⟧n ρ)
                      = cancel-sound′ a (b + et ρ (j , y)) ((i , x) ∷ nf₁) nf₂ ρ H
cancel-sound′ a b ((i , x) ∷ nf₁) ((j , .x) ∷ nf₂) ρ H | equal refl
  with compare i j
cancel-sound′ a b ((i , x) ∷ nf₁) ((.(suc k + i) , .x) ∷ nf₂) ρ H | equal refl | less (diff! k)
  rewrite fst-*** id (List._∷_ (suc k , x)) (cancel nf₁ nf₂)
        | snd-*** id (List._∷_ (suc k , x)) (cancel nf₁ nf₂)
        | add-assoc b (et ρ (suc k , x)) (⟦ snd (cancel nf₁ nf₂) ⟧n ρ)
        | shuffle₁ a (et ρ (i , x)) (⟦ nf₁ ⟧n ρ)
        | cancel-sound′ a (b + et ρ (suc k , x)) nf₁ nf₂ ρ H
        = tactic auto
cancel-sound′ a b ((.(suc k + j) , x) ∷ nf₁) ((j , .x) ∷ nf₂) ρ H | equal refl | greater (diff! k)
  rewrite fst-*** (List._∷_ (suc k , x)) id (cancel nf₁ nf₂)
        | snd-*** (List._∷_ (suc k , x)) id (cancel nf₁ nf₂)
        | add-assoc a (et ρ (suc k , x)) (⟦ fst (cancel nf₁ nf₂) ⟧n ρ)
        | shuffle₁ b (et ρ (j , x)) (⟦ nf₂ ⟧n ρ)
        | sym (cancel-sound′ (a + et ρ (suc k , x)) b nf₁ nf₂ ρ H)
        = tactic auto
cancel-sound′ a b ((i , x) ∷ nf₁) ((.i , .x) ∷ nf₂) ρ H | equal refl | equal refl
  rewrite shuffle₁ a (et ρ (i , x)) (⟦ nf₁ ⟧n ρ)
        | cancel-sound′ a b nf₁ nf₂ ρ H
        = tactic auto

cancel-sound : ∀ nf₁ nf₂ ρ → NFEqS (cancel nf₁ nf₂) ρ → NFEq (nf₁ , nf₂) ρ
cancel-sound nf₁ nf₂ ρ H rewrite cong (λ p → NFEqS p ρ) (eta (cancel nf₁ nf₂))
                              | ns-sound (fst (cancel nf₁ nf₂)) ρ
                              | ns-sound (snd (cancel nf₁ nf₂)) ρ
                              = cancel-sound′ 0 0 nf₁ nf₂ ρ H

prod : Env → List Nat → Nat
prod ρ x = product (map ρ x)

private
  shuffle₂ : ∀ a b c d e → a + (b + c + d + e) ≡ c + (a + (b + d) + e)
  shuffle₂ a b c d e = tactic auto

  shuffle₃ : ∀ a b c d → a + (b + c + d) ≡ a + (b + c) + d
  shuffle₃ a b c d = tactic auto

cancel-complete′ : ∀ a b nf₁ nf₂ ρ →
                     a + ⟦ nf₁ ⟧n ρ ≡ b + ⟦ nf₂ ⟧n ρ →
                     a + ⟦ fst (cancel nf₁ nf₂) ⟧n ρ ≡ b + ⟦ snd (cancel nf₁ nf₂) ⟧n ρ
cancel-complete′ a b [] [] ρ H = H
cancel-complete′ a b [] (x ∷ nf₂) ρ H = H
cancel-complete′ a b (x ∷ nf₁) [] ρ H = H
cancel-complete′ a b ((i , x) ∷ nf₁) ((j , y) ∷ nf₂) ρ H with compare x y
... | less lt
  rewrite fst-*** (List._∷_ (i , x)) id (cancel nf₁ ((j , y) ∷ nf₂))
        | snd-*** (List._∷_ (i , x)) id (cancel nf₁ ((j , y) ∷ nf₂))
        | add-assoc a (et ρ (i , x)) (⟦ fst (cancel nf₁ ((j , y) ∷ nf₂)) ⟧n ρ)
        | add-assoc a (et ρ (i , x)) (⟦ nf₁ ⟧n ρ)
        = cancel-complete′ (a + et ρ (i , x)) b nf₁ ((j , y) ∷ nf₂) ρ H
... | greater _ rewrite fst-*** id (List._∷_ (j , y)) (cancel ((i , x) ∷ nf₁) nf₂)
                      | snd-*** id (List._∷_ (j , y)) (cancel ((i , x) ∷ nf₁) nf₂)
                      | add-assoc b (et ρ (j , y)) (⟦ snd (cancel ((i , x) ∷ nf₁) nf₂) ⟧n ρ)
                      | add-assoc b (et ρ (j , y)) (⟦ nf₂ ⟧n ρ)
                      = cancel-complete′ a (b + et ρ (j , y)) ((i , x) ∷ nf₁) nf₂ ρ H
cancel-complete′ a b ((i , x) ∷ nf₁) ((j , .x) ∷ nf₂) ρ H | equal refl with compare i j
cancel-complete′ a b ((i , x) ∷ nf₁) ((.(suc (k + i)) , .x) ∷ nf₂) ρ H | equal refl | less (diff! k)
  rewrite fst-*** id (List._∷_ (suc k , x)) (cancel nf₁ nf₂)
        | snd-*** id (List._∷_ (suc k , x)) (cancel nf₁ nf₂)
        | shuffle₁ a (i * prod ρ x) (⟦ nf₁ ⟧n ρ)
        | mul-distr-r k i (prod ρ x)
        | shuffle₂ b (k * prod ρ x) (i * prod ρ x) (prod ρ x) (⟦ nf₂ ⟧n ρ)
        | cancel-complete′ a (b + suc k * prod ρ x) nf₁ nf₂ ρ (add-inj₂ (i * prod ρ x) _ _ H)
        = tactic auto
cancel-complete′ a b ((.(suc (k + j)) , x) ∷ nf₁) ((j , .x) ∷ nf₂) ρ H | equal refl | greater (diff! k)
  rewrite fst-*** (List._∷_ (suc k , x)) id (cancel nf₁ nf₂)
        | snd-*** (List._∷_ (suc k , x)) id (cancel nf₁ nf₂)
        | shuffle₁ b (j * prod ρ x) (⟦ nf₂ ⟧n ρ)
        | mul-distr-r k j (prod ρ x)
        | shuffle₂ a (k * prod ρ x) (j * prod ρ x) (prod ρ x) (⟦ nf₁ ⟧n ρ)
        | shuffle₃ a (k * prod ρ x) (prod ρ x) (⟦ fst (cancel nf₁ nf₂) ⟧n ρ)
        | cancel-complete′ (a + suc k * prod ρ x) b nf₁ nf₂ ρ (add-inj₂ (j * prod ρ x) _ _ H)
        = refl
cancel-complete′ a b ((i , x) ∷ nf₁) ((.i , .x) ∷ nf₂) ρ H | equal refl | equal refl
  rewrite shuffle₁ a (i * prod ρ x) (⟦ nf₁ ⟧n ρ)
        | shuffle₁ b (i * prod ρ x) (⟦ nf₂ ⟧n ρ)
        = cancel-complete′ a b nf₁ nf₂ ρ (add-inj₂ (i * prod ρ x) _ _ H)

cancel-complete : ∀ nf₁ nf₂ ρ → NFEq (nf₁ , nf₂) ρ → NFEqS (cancel nf₁ nf₂) ρ
cancel-complete nf₁ nf₂ ρ H
  rewrite cong (λ p → NFEqS p ρ) (eta (cancel nf₁ nf₂))
        | ns-sound (fst (cancel nf₁ nf₂)) ρ
        | ns-sound (snd (cancel nf₁ nf₂)) ρ
        = cancel-complete′ 0 0 nf₁ nf₂ ρ H
