{-# OPTIONS -v profile.interactive:10 #-}
module Data.Rational where

open import Prelude
open import Data.Nat.GCD
open import Data.Nat.Prime
open import Data.Nat.Divide
open import Data.Nat.Properties
open import Tactic.Nat

data Rational : Set where
  ratio : (p q : Nat) {{nz : NonZero q}} (prf : Coprime p q) → Rational

numerator : Rational → Nat
numerator (ratio p _ _) = p

denominator : Rational → Nat
denominator (ratio _ q _) = q

private
  lem-divide-mul : ∀ a b {{_ : NonZero b}} → (a * b) Divides b → a ≡ 1
  lem-divide-mul _        0 {{}}
  lem-divide-mul  0      (suc b) (factor  q      eq) = refute eq
  lem-divide-mul (suc a) (suc b) (factor  0      eq) = refute eq
  lem-divide-mul (suc a) (suc b) (factor (suc q) eq) = by eq

  nonzero-gcd : ∀ a b {{_ : NonZero b}} → NonZero (gcd! a b)
  nonzero-gcd _ 0 {{}}
  nonzero-gcd a (suc b) with gcd a (suc b)
  nonzero-gcd a (suc b) | gcd-res 0 d|a d|b g = refute (divides-zero d|b)
  nonzero-gcd a (suc b) | gcd-res (suc d) d|a d|b g = _

  mkratio-lem : ∀ p q d p′ q′ {{_ : NonZero q}} →
                p′ * d ≡ p →
                q′ * d ≡ q →
                (∀ k → k Divides p → k Divides q → k Divides d) →
                gcd! p′ q′ ≡ 1
  mkratio-lem p q d p′ q′ eqp eqq g with gcd p′ q′
  mkratio-lem ._ ._ d ._ ._ refl refl g
    | gcd-res d′ (factor! p₂) (factor! q₂) g′ =
    let p′ = p₂ * d′
        q′ = q₂ * d′
        p = p′ * d
        q = q′ * d
        nzd : NonZero d
        nzd = transport NonZero (gcd-unique p q d (factor! p′) (factor! q′) g) (nonzero-gcd p q)
        dd′|d : (d′ * d) Divides d
        dd′|d = g (d′ * d) (factor p₂ auto) (factor q₂ auto)
    in lem-divide-mul d′ d dd′|d

  lem-nonzero-mul-l : ∀ a b c {{_ : NonZero c}} → a * b ≡ c → NonZero a
  lem-nonzero-mul-l  0      b .0 {{}} refl
  lem-nonzero-mul-l (suc a) b  c eq = _

  lem-nonzero-mul : ∀ a b {{_ : NonZero a}} {{_ : NonZero b}} → NonZero (a * b)
  lem-nonzero-mul zero b {{}}
  lem-nonzero-mul a zero {{_}} {{}}
  lem-nonzero-mul (suc a) (suc b) = transport NonZero {x = suc (a * suc b + b)} auto _

infixl 7 mkratio
syntax mkratio p q = p :/ q
mkratio : (p q : Nat) {{_ : NonZero q}} → Rational
mkratio p q with gcd p q
... | gcd-res d (factor p′ eq) (factor q′ eq₁) g =
  ratio p′ q′ {{lem-nonzero-mul-l q′ d q eq₁}} (mkratio-lem p q d p′ q′ eq eq₁ g)

mkratio-sound : (p q : Nat) {{_ : NonZero q}} → p * denominator (mkratio p q) ≡ q * numerator (mkratio p q)
mkratio-sound p q with gcd p q
mkratio-sound ._ ._ | gcd-res d (factor! p′) (factor! q′) _ = auto

NonZeroQ : Rational → Set
NonZeroQ (ratio 0 _ _) = ⊥
NonZeroQ (ratio (suc n) _ _) = ⊤

infixl 6 _+Q_ _-Q_
infixl 7 _*Q_ _/Q_

_+Q_ : Rational → Rational → Rational
ratio p q _ +Q ratio p₁ q₁ _ = mkratio (p * q₁ + p₁ * q) (q * q₁) {{lem-nonzero-mul q q₁}}

_-Q_ : Rational → Rational → Rational
ratio p q _ -Q ratio p₁ q₁ _ = mkratio (p * q₁ - p₁ * q) (q * q₁) {{lem-nonzero-mul q q₁}}

_*Q_ : Rational → Rational → Rational
ratio p q _ *Q ratio p₁ q₁ _ = mkratio (p * p₁) (q * q₁) {{lem-nonzero-mul q q₁}}

recip : (x : Rational) {{_ : NonZeroQ x}} → Rational
recip (ratio 0 q eq) {{}}
recip (ratio (suc p) q eq) = ratio q (suc p) (gcd-commute q (suc p) ⟨≡⟩ eq)

_/Q_ : (x y : Rational) {{_ : NonZeroQ y}} → Rational
x /Q y = x *Q recip y

instance
  FracQ : Fractional Rational
  Fractional.Constraint FracQ _ y = NonZeroQ y
  Fractional._/_        FracQ x y = x /Q y

{-# DISPLAY _+Q_ a b = a + b #-}
{-# DISPLAY _-Q_ a b = a - b #-}
{-# DISPLAY _*Q_ a b = a * b #-}
{-# DISPLAY ratio a b refl = a / b #-}

instance
  NumberRational : Number Rational
  NumberRational = record { Constraint = λ _ → ⊤ ; fromNat = λ n → n :/ 1 }

  SemiringRational : Semiring Rational
  SemiringRational = record { zro = 0 :/ 1 ; one = 1 :/ 1
                            ; _+_ = _+Q_ ; _*_ = _*Q_ }
