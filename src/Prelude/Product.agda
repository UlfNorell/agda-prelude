
module Prelude.Product where

open import Agda.Primitive
open import Prelude.Function

infixr 1 _,_
record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
 constructor _,_
 field
   fst : A
   snd : B fst

open Σ public

infixr 3 _×_
_×_ : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
A × B = Σ A (const B)

uncurry : ∀ {a b c} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c} →
            (∀ x (y : B x) → C x y) → (p : Σ A B) → C (fst p) (snd p)
uncurry f (x , y) = f x y

curry : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Σ A B → Set c} →
          (∀ p → C p) → ∀ x (y : B x) → C (x , y)
curry f x y = f (x , y)

infixr 3 _***_ _&&&_
_***_ : ∀ {a₁ a₂ b₁ b₂} {A₁ : Set a₁} {A₂ : Set a₂} {B₁ : A₁ → Set b₁} {B₂ : A₂ → Set b₂}
          (f : A₁ → A₂) → (∀ {x} → B₁ x → B₂ (f x)) → Σ A₁ B₁ → Σ A₂ B₂
(f *** g) (x , y) = f x , g y

_&&&_ : ∀ {c a b} {C : Set c} {A : Set a} {B : A → Set b}
          (f : C → A) → (∀ x → B (f x)) → C → Σ A B
(f &&& g) x = f x , g x

first : ∀ {a₁ a₂ b} {A₁ : Set a₁} {A₂ : Set a₂} {B : Set b} →
          (A₁ → A₂) → A₁ × B → A₂ × B
first f = f *** id

second : ∀ {a b₁ b₂} {A : Set a} {B₁ : A → Set b₁} {B₂ : A → Set b₂} →
           (∀ {x} → B₁ x → B₂ x) → Σ A B₁ → Σ A B₂
second f = id *** f
