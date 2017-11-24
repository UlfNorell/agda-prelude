
module Prelude.Nat.Properties where

open import Prelude.Bool
open import Prelude.Nat.Core
open import Prelude.Equality
open import Prelude.Semiring

suc-inj : ∀ {n m} → suc n ≡ suc m → n ≡ m
suc-inj refl = refl

--- Addition ---

add-zero-r : (n : Nat) → n + 0 ≡ n
add-zero-r zero    = refl
add-zero-r (suc n) = suc $≡ add-zero-r n

add-suc-r : (n m : Nat) → n + suc m ≡ suc (n + m)
add-suc-r zero    m = refl
add-suc-r (suc n) m = suc $≡ add-suc-r n m

add-commute : (a b : Nat) → a + b ≡ b + a
add-commute zero    b = sym (add-zero-r _)
add-commute (suc a) b = suc $≡ add-commute a b ⟨≡⟩ʳ add-suc-r b _

add-assoc : (a b c : Nat) → a + (b + c) ≡ a + b + c
add-assoc zero    b c = refl
add-assoc (suc a) b c = suc $≡ add-assoc a b c

add-inj₂ : (a b c : Nat) → a + b ≡ a + c → b ≡ c
add-inj₂ zero    b c eq = eq
add-inj₂ (suc a) b c eq = add-inj₂ a b c (suc-inj eq)

add-inj₁ : (a b c : Nat) → a + c ≡ b + c → a ≡ b
add-inj₁ a b c eq = add-inj₂ c a b (add-commute c a ⟨≡⟩ eq ⟨≡⟩ add-commute b c)

--- Subtraction ---

--- Multiplication ---

mul-one-r : (x : Nat) → x * 1 ≡ x
mul-one-r zero    = refl
mul-one-r (suc x) = suc $≡ mul-one-r x

mul-zero-r : (x : Nat) → x * 0 ≡ 0
mul-zero-r zero    = refl
mul-zero-r (suc x) = mul-zero-r x

mul-distr-r : (x y z : Nat) → (x + y) * z ≡ x * z + y * z
mul-distr-r zero    y z = refl
mul-distr-r (suc x) y z = z +_ $≡ mul-distr-r x y z ⟨≡⟩ add-assoc z _ _

private
  shuffle : (a b c d : Nat) → a + b + (c + d) ≡ a + c + (b + d)
  shuffle a b c d = add-assoc a _ _ ʳ⟨≡⟩
                    a +_ $≡ (add-assoc b c d ⟨≡⟩ _+ d $≡ add-commute b c ⟨≡⟩ʳ add-assoc c b d) ⟨≡⟩
                    add-assoc a _ _

mul-distr-l : (x y z : Nat) → x * (y + z) ≡ x * y + x * z
mul-distr-l zero    y z = refl
mul-distr-l (suc x) y z = y + z +_ $≡ mul-distr-l x y z ⟨≡⟩ shuffle y z (x * y) (x * z)

mul-assoc : (x y z : Nat) → x * (y * z) ≡ x * y * z
mul-assoc zero    y z = refl
mul-assoc (suc x) y z = y * z +_ $≡ mul-assoc x y z ⟨≡⟩ʳ mul-distr-r y (x * y) z

mul-commute : (x y : Nat) → x * y ≡ y * x
mul-commute x zero    = mul-zero-r x
mul-commute x (suc y) = mul-distr-l x 1 y ⟨≡⟩ _+ x * y $≡ mul-one-r x ⟨≡⟩ x +_ $≡ mul-commute x y

mul-inj₁ : (x y z : Nat) {{_ : NonZero z}} → x * z ≡ y * z → x ≡ y
mul-inj₁ x        y      zero {{}}
mul-inj₁ zero     zero   (suc z) eq = refl
mul-inj₁ zero    (suc y) (suc z) ()
mul-inj₁ (suc x) zero    (suc z) ()
mul-inj₁ (suc x) (suc y) (suc z) eq = suc $≡ mul-inj₁ x y (suc z) (add-inj₂ z _ _ (suc-inj eq))

mul-inj₂ : (x y z : Nat) {{_ : NonZero x}} → x * y ≡ x * z → y ≡ z
mul-inj₂ x y z eq = mul-inj₁ y z x (mul-commute y x ⟨≡⟩ eq ⟨≡⟩ mul-commute x z)
