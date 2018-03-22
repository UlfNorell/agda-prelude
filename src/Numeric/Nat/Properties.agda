
module Numeric.Nat.Properties where

open import Prelude hiding (less-antisym; less-antirefl; leq-antisym)
open import Prelude.Nat.Properties public
open import Tactic.Nat

--- Subtraction ---

sub-less : {a b : Nat} → a ≤ b → b - a + a ≡ b
sub-less {zero} _ = auto
sub-less {suc a} (diff! k) = auto

sub-underflow : (a b : Nat) → a ≤ b → a - b ≡ 0
sub-underflow a ._ (diff! k) = auto

sub-leq : (a b : Nat) → a - b ≤ a
sub-leq a b with compare a b
sub-leq a ._ | less    (diff! k) = diff a auto
sub-leq a .a | equal    refl     = diff a auto
sub-leq ._ b | greater (diff! k) = diff b auto

--- LessNat ---

fast-diff : {a b : Nat} → a < b → a < b
fast-diff {a} {b} a<b = diff (b - suc a) (eraseEquality $ by (sub-less {suc a} {b} (by a<b)))
{-# INLINE fast-diff #-}

infixr 0 _⟨<⟩_ _⟨≤⟩_

_⟨<⟩_ : ∀ {x y z} → LessNat x y → LessNat y z → LessNat x z
diff! a ⟨<⟩ diff! b = diff (suc (b + a)) auto

less-antirefl : ∀ {a b : Nat} → a < b → ¬ (a ≡ b)
less-antirefl (diff! k) eq = refute eq

less-not-geq : ∀ {a b : Nat} → a < b → b ≤ a → ⊥
less-not-geq (diff d eq) (diff! d₁) = refute eq

less-raa : {a b : Nat} → ¬ (suc a > b) → a < b
less-raa {a} {b} a≱b with compare a b
less-raa a≱b | less    a<b = a<b
less-raa a≱b | equal  refl = ⊥-elim (a≱b auto)
less-raa a≱b | greater a>b = ⊥-elim (a≱b (by a>b))

_⟨≤⟩_ : {a b c : Nat} → a ≤ b → b ≤ c → a ≤ c
diff! k ⟨≤⟩ diff! k₁ = auto

private
  less-mul-r′ : ∀ a b → NonZero b → a ≤ a * b
  less-mul-r′ _  zero ()
  less-mul-r′ a (suc b) _ = auto

less-mul-r : ∀ a b {{_ : NonZero b}} → a ≤ a * b
less-mul-r a b = fast-diff (less-mul-r′ _ b it)

add-nonzero-l : ∀ a b {{_ : NonZero a}} → NonZero (a + b)
add-nonzero-l zero    b {{}}
add-nonzero-l (suc a) b = _

add-nonzero-r : ∀ a b {{_ : NonZero b}} → NonZero (a + b)
add-nonzero-r zero    zero {{}}
add-nonzero-r zero    (suc b) = _
add-nonzero-r (suc a) b       = _

mul-nonzero : ∀ a b {{nza : NonZero a}} {{nzb : NonZero b}} → NonZero (a * b)
mul-nonzero zero    b    {{nza = ()}}
mul-nonzero (suc a) zero {{nzb = ()}}
mul-nonzero (suc a) (suc b) = _

mul-nonzero-l : ∀ a b {{_ : NonZero (a * b)}} → NonZero a
mul-nonzero-l 0 _ {{}}
mul-nonzero-l (suc _) _ = _

mul-nonzero-r : ∀ a b {{_ : NonZero (a * b)}} → NonZero b
mul-nonzero-r a b {{nz}} = mul-nonzero-l b a {{transport NonZero auto nz}}

mul-unit-l : ∀ a b {{_ : NonZero b}} → a * b ≡ b → a ≡ 1
mul-unit-l 1 _ _ = refl
mul-unit-l 0 .0 {{}} refl
mul-unit-l (suc (suc a)) zero {{}} _
mul-unit-l (suc (suc a)) (suc b) ab=b = refute ab=b

mul-unit-r : ∀ a b {{_ : NonZero a}} → a * b ≡ a → b ≡ 1
mul-unit-r a b ab=a = mul-unit-l b a (mul-commute b a ⟨≡⟩ ab=a)
