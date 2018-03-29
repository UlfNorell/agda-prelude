
module Numeric.Nat.Divide.Properties where

open import Prelude
open import Numeric.Nat.Properties
open import Numeric.Nat.DivMod
open import Numeric.Nat.Divide
open import Tactic.Nat

divides-add : ∀ {a b d} → d Divides a → d Divides b → d Divides (a + b)
divides-add (factor! q) (factor! q₁) = factor (q + q₁) auto

divides-mul-r : ∀ a {b d} → d Divides b → d Divides (a * b)
divides-mul-r a (factor! q) = factor (a * q) auto

divides-mul-l : ∀ {a} b {d} → d Divides a → d Divides (a * b)
divides-mul-l b (factor! q) = factor (b * q) auto

divides-mul : ∀ {a b c d} → c Divides a → d Divides b → (c * d) Divides (a * b)
divides-mul (factor! q) (factor! r) = factor (q * r) auto

mul-divides-l : (a b c : Nat) → (a * b) Divides c → a Divides c
mul-divides-l a b c (factor! q) = factor (q * b) auto

mul-divides-r : (a b c : Nat) → (a * b) Divides c → b Divides c
mul-divides-r a b c (factor! q) = factor (q * a) auto

divides-flip-mul : ∀ {a b c d} → c Divides b → d Divides a → (c * d) Divides (a * b)
divides-flip-mul {a} {b} {c} {d} c|b d|a =
  transport ((c * d) Divides_) (mul-commute b a) (divides-mul c|b d|a)

divides-sub-l : ∀ {a b d} → d Divides (a + b) → d Divides a → d Divides b
divides-sub-l {b = b} {d} (factor q₁ eq) (factor! q) = factor (q₁ - q) $ by eq

divides-sub-r : ∀ {a b d} → d Divides (a + b) → d Divides b → d Divides a
divides-sub-r {a} {b} d|ab d|b rewrite add-commute a b = divides-sub-l d|ab d|b

divides-mul-cong-l : ∀ {a b} c → a Divides b → (c * a) Divides (c * b)
divides-mul-cong-l {a} {b} c (factor q eq) = factor q (by (c *_ $≡ eq))

divides-mul-cong-r : ∀ {a b} c → a Divides b → (a * c) Divides (b * c)
divides-mul-cong-r {a} {b} c (factor q eq) = factor q (by (c *_ $≡ eq))

divides-nonzero : ∀ {a b} {{_ : NonZero b}} → a Divides b → NonZero a
divides-nonzero {zero} {{nzb}} (factor! b) = transport NonZero (mul-zero-r b) nzb
divides-nonzero {suc _} _ = _

divides-refl : ∀ {a} → a Divides a
divides-refl = factor 1 auto

divides-antisym : ∀ {a b} → a Divides b → b Divides a → a ≡ b
divides-antisym         (factor! q)       (factor! 0)                = auto
divides-antisym         (factor! q)       (factor 1 eq)              = by eq
divides-antisym {zero}  (factor! q)       (factor (suc (suc q₁)) eq) = auto
divides-antisym {suc a} (factor! 0)       (factor (suc (suc q₁)) eq) = by eq
divides-antisym {suc a} (factor! (suc q)) (factor (suc (suc q₁)) eq) = refute eq

divides-trans : ∀ {a b c} → a Divides b → b Divides c → a Divides c
divides-trans (factor! q) (factor! q′) = factor (q′ * q) auto

divides-zero : ∀ {a} → 0 Divides a → a ≡ 0
divides-zero (factor! q) = auto

one-divides : ∀ {a} → 1 Divides a
one-divides {a} = factor a auto

divides-one : ∀ {a} → a Divides 1 → a ≡ 1
divides-one {0} (factor k eq) = refute eq
divides-one {1} _ = refl
divides-one {suc (suc a)} (factor zero ())
divides-one {suc (suc a)} (factor (suc k) eq) = refute eq

divides-less : ∀ {a b} {{_ : NonZero b}} → a Divides b → a ≤ b
divides-less {{}} (factor! 0)
divides-less {a} (factor! (suc q)) = auto

nonzero-factor : ∀ {a b} ⦃ nzb : NonZero b ⦄ (a|b : a Divides b) → NonZero (get-factor a|b)
nonzero-factor ⦃ () ⦄ (factor! zero)
nonzero-factor (factor! (suc _)) = _
