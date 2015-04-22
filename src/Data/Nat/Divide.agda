
module Data.Nat.Divide where

open import Prelude
open import Control.WellFounded
open import Data.Nat.Properties
open import Data.Nat.DivMod
open import Tactic.Nat

--- Divides predicate ---

data _Divides_ (a b : Nat) : Set where
  factor : ∀ q (eq : q * a ≡ b) → a Divides b

pattern factor! q = factor q refl
{-# DISPLAY factor q refl = factor! q #-}

divides-divmod : ∀ {a b} {{_ : NonZero b}} → b Divides a → DivMod a b
divides-divmod {b = zero } {{}}
divides-divmod {b = suc b} (factor q eq) = qr q 0 auto (by eq)

divides-add : ∀ {a b d} → d Divides a → d Divides b → d Divides (a + b)
divides-add (factor! q) (factor! q₁) = factor (q + q₁) auto

divides-mul-r : ∀ a {b d} → d Divides b → d Divides (a * b)
divides-mul-r a (factor! q) = factor (a * q) auto

divides-mul-l : ∀ {a} b {d} → d Divides a → d Divides (a * b)
divides-mul-l b (factor! q) = factor (b * q) auto

divides-sub-l : ∀ {a b d} → d Divides (a + b) → d Divides a → d Divides b
divides-sub-l {b = b} {d} (factor q₁ eq) (factor! q) = factor (q₁ - q) $ by eq

divides-sub-r : ∀ {a b d} → d Divides (a + b) → d Divides b → d Divides a
divides-sub-r {a} {b} d|ab d|b rewrite add-commute a b = divides-sub-l d|ab d|b

mod-divides : ∀ {a b} {{_ : NonZero a}} → a Divides b → b mod a ≡ 0
mod-divides {zero} {{}}
mod-divides {suc a} {b} (factor q eq) =
  rem-unique (b divmod suc a) (divides-divmod (factor q eq))

div-divides : ∀ {a b} {{_ : NonZero a}} → a Divides b → (b div a) * a ≡ b
div-divides {a} {b} a|b with divmod-sound a b
... | eq rewrite mod-divides a|b = by eq

divides-refl : ∀ {a} → a Divides a
divides-refl = factor! 1

divides-antisym : ∀ {a b} → a Divides b → b Divides a → a ≡ b
divides-antisym         (factor! q)       (factor! 0)                = auto
divides-antisym         (factor! q)       (factor 1 eq)              = sym eq
divides-antisym {zero}  (factor! q)       (factor (suc (suc q₁)) eq) = auto
divides-antisym {suc a} (factor! 0)       (factor (suc (suc q₁)) eq) = by eq
divides-antisym {suc a} (factor! (suc q)) (factor (suc (suc q₁)) eq) = refute eq

divides-trans : ∀ {a b c} → a Divides b → b Divides c → a Divides c
divides-trans (factor! q) (factor! q′) = factor (q′ * q) auto

divides-zero : ∀ {a} → 0 Divides a → a ≡ 0
divides-zero (factor! q) = auto

divides-less : ∀ {a b} {{_ : NonZero b}} → a Divides b → a ≤ b
divides-less {{}} (factor! 0)
divides-less {a} (factor! (suc q)) = auto

private
  safediv : Nat → Nat → Nat
  safediv a 0 = 0
  safediv a (suc b) = a div suc b

  divides-safediv : ∀ {a b} → a Divides b → safediv b a * a ≡ b
  divides-safediv {zero } 0|b = sym (divides-zero 0|b)
  divides-safediv {suc a} a|b = div-divides a|b

fast-divides : ∀ {a b} → a Divides b → a Divides b
fast-divides {a} {b} a|b = factor (safediv b a) (eraseEquality (divides-safediv a|b))

private
  no-divides-suc-mod : ∀ {a b} q {r} → LessNat (suc r) a → q * a + suc r ≡ b → ¬ (a Divides b)
  no-divides-suc-mod {zero} _ (diff _ ())
  no-divides-suc-mod {suc a} q {r} lt eq (factor q′ eq′) =
    refute (rem-unique
              (divides-divmod (factor q′ eq′))
              (qr q (suc r) lt eq))

  no-divides-zero : ∀ {a} → ¬ (0 Divides suc a)
  no-divides-zero {a} (factor q eq) = refute eq

_divides?_ : ∀ a b → Dec (a Divides b)
a     divides? zero  = yes (factor! 0)
zero  divides? suc b = no no-divides-zero
suc a divides? suc b with suc b divmod suc a
suc a divides? suc b | qr q  zero    _ eq  = yes (factor q (by eq))
suc a divides? suc b | qr q (suc r) lt eq₁ = no (no-divides-suc-mod q lt eq₁)
