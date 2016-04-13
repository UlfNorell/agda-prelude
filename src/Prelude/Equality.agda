
module Prelude.Equality where

open import Prelude.Decidable

open import Agda.Builtin.Equality public

record Eq {a} (A : Set a) : Set a where
  infix 4 _==_
  field
    _==_ : (x y : A) → Dec (x ≡ y)

open Eq {{...}} public

sym : ∀ {a} {A : Set a} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

infixr 0 _⟨≡⟩_ _⟨≡⟩ʳ_ _ʳ⟨≡⟩_ _ʳ⟨≡⟩ʳ_

trans : ∀ {a} {A : Set a} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl eq = eq

_⟨≡⟩_ = trans

_⟨≡⟩ʳ_ : ∀ {a} {A : Set a} {x y z : A} → x ≡ y → z ≡ y → x ≡ z
eq ⟨≡⟩ʳ refl = eq

_ʳ⟨≡⟩_ : ∀ {a} {A : Set a} {x y z : A} → y ≡ x → y ≡ z → x ≡ z
refl ʳ⟨≡⟩ eq = eq

_ʳ⟨≡⟩ʳ_ : ∀ {a} {A : Set a} {x y z : A} → y ≡ x → z ≡ y → x ≡ z
refl ʳ⟨≡⟩ʳ refl = refl

infixl 4 cong _*≡_
syntax cong f eq = f $≡ eq
cong : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

_*≡_ : ∀ {a b} {A : Set a} {B : Set b} {f g : A → B} {x y} → f ≡ g → x ≡ y → f x ≡ g y
refl *≡ refl = refl

cong₂ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} (f : A → B → C) {x₁ x₂ y₁ y₂} →
        x₁ ≡ x₂ → y₁ ≡ y₂ → f x₁ y₁ ≡ f x₂ y₂
cong₂ f refl refl = refl

transport : ∀ {a b} {A : Set a} (B : A → Set b) {x y} → x ≡ y → B x → B y
transport B refl bx = bx

transport₂ : ∀ {a b c} {A : Set a} {B : Set b} (C : A → B → Set c) {x₁ x₂ y₁ y₂} → x₁ ≡ x₂ → y₁ ≡ y₂ → C x₁ y₁ → C x₂ y₂
transport₂ C refl refl cxy = cxy

-- Decidable equality helpers --

decEq₁ : ∀ {a b} {A : Set a} {B : Set b} {f : A → B} → (∀ {x y} → f x ≡ f y → x ≡ y) →
           ∀ {x y} → Dec (x ≡ y) → Dec (f x ≡ f y)
decEq₁ f-inj (yes refl) = yes refl
decEq₁ f-inj (no  neq)  = no λ eq → neq (f-inj eq)

decEq₂ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} {f : A → B → C} →
           (∀ {x y z w} → f x y ≡ f z w → x ≡ z) →
           (∀ {x y z w} → f x y ≡ f z w → y ≡ w) →
           ∀ {x y z w} → Dec (x ≡ y) → Dec (z ≡ w) → Dec (f x z ≡ f y w)
decEq₂ f-inj₁ f-inj₂ (no neq)    _         = no λ eq → neq (f-inj₁ eq)
decEq₂ f-inj₁ f-inj₂  _         (no neq)   = no λ eq → neq (f-inj₂ eq)
decEq₂ f-inj₁ f-inj₂ (yes refl) (yes refl) = yes refl

{-# INLINE decEq₁ #-}
{-# INLINE decEq₂ #-}

-- Equality reasoning --

infixr 0 _≡⟨_⟩_ _≡⟨_⟩ʳ_
infix  1 _∎

_≡⟨_⟩_ : ∀ {a} {A : Set a} (x : A) {y z} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ refl ⟩ p = p

_≡⟨_⟩ʳ_ : ∀ {a} {A : Set a} (x : A) {y z} → y ≡ x → y ≡ z → x ≡ z
x ≡⟨ refl ⟩ʳ p = p

_∎ : ∀ {a} {A : Set a} (x : A) → x ≡ x
x ∎ = refl

-- Instances --

instance
  EqEq : ∀ {a} {A : Set a} {x y : A} → Eq (x ≡ y)
  _==_ {{EqEq}} refl refl = yes refl
