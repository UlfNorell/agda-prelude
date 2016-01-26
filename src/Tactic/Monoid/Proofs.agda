
module Tactic.Monoid.Proofs where

open import Prelude
open import Data.Monoid
open import Data.Monoid.Laws

open import Tactic.Monoid.Exp

⟦_⟧_ : ∀ {a} {A : Set a} {{_ : Monoid A}} → Exp → (Nat → A) → A
⟦ var x  ⟧ ρ = ρ x
⟦ ε      ⟧ ρ = mempty
⟦ e ⊕ e₁ ⟧ ρ = ⟦ e ⟧ ρ <> ⟦ e₁ ⟧ ρ

⟦_⟧n_ : ∀ {a} {A : Set a} {{_ : Monoid A}} → List Nat → (Nat → A) → A
⟦ xs ⟧n ρ = mconcat (map ρ xs)

map/++ : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) (xs ys : List A) → map f (xs ++ ys) ≡ map f xs ++ map f ys
map/++ f [] ys = refl
map/++ f (x ∷ xs) ys = f x ∷_ $≡ map/++ f xs ys

module _ {a} {A : Set a} {{Mon : Monoid A}} {{Laws : MonoidLaws A}} where

  mconcat/++ : (xs ys : List A) → mconcat (xs ++ ys) ≡ mconcat xs <> mconcat ys
  mconcat/++ [] ys = sym (idLeft _)
  mconcat/++ (x ∷ xs) ys = x <>_ $≡ mconcat/++ xs ys ⟨≡⟩ <>assoc x _ _

  sound : ∀ e (ρ : Nat → A) → ⟦ e ⟧ ρ ≡ ⟦ flatten e ⟧n ρ
  sound (var x) ρ = sym (idRight (ρ x))
  sound ε ρ = refl
  sound (e ⊕ e₁) ρ = _<>_ $≡ sound e ρ *≡ sound e₁ ρ ⟨≡⟩ʳ
                     mconcat $≡ map/++ ρ (flatten e) (flatten e₁) ⟨≡⟩
                     mconcat/++ (map ρ (flatten e)) _

  proof : ∀ e e₁ (ρ : Nat → A) → flatten e ≡ flatten e₁ → ⟦ e ⟧ ρ ≡ ⟦ e₁ ⟧ ρ
  proof e e₁ ρ nfeq = eraseEquality $ sound e ρ ⟨≡⟩ (⟦_⟧n ρ) $≡ nfeq ⟨≡⟩ʳ sound e₁ ρ


