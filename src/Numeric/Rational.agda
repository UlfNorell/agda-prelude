
module Numeric.Rational where

open import Prelude
open import Numeric.Nat.GCD
open import Numeric.Nat.GCD.Extended
open import Numeric.Nat.GCD.Properties
open import Numeric.Nat.Prime
open import Numeric.Nat.Prime.Properties
open import Numeric.Nat.Divide
open import Numeric.Nat.Divide.Properties
open import Numeric.Nat.Properties
open import Tactic.Nat
open import Tactic.Nat.Coprime

record Rational : Set where
  no-eta-equality
  constructor ratio
  field numerator   : Nat
        denominator : Nat
        ⦃ d>0 ⦄    : NonZero denominator
        n⊥d        : Coprime numerator denominator

open Rational public using (numerator; denominator)

infixl 7 mkratio
syntax mkratio p q = p :/ q
mkratio : (p q : Nat) {{_ : NonZero q}} → Rational
mkratio p q = gcdReduce-r p q λ p′ q′ _ _ _ prf → ratio p′ q′ prf

mkratio-sound : (p q : Nat) {{_ : NonZero q}} → p * denominator (mkratio p q) ≡ q * numerator (mkratio p q)
mkratio-sound p q with gcd p q
... | gcd-res d (is-gcd (factor! p′) (factor! q′) _) = auto

NonZeroQ : Rational → Set
NonZeroQ x = NonZero (numerator x)

infixl 6 _+Q_ _-Q_
infixl 7 _*Q_ _/Q_

_+Q_ : Rational → Rational → Rational
ratio n₁ d₁ n₁/d₁ +Q ratio n₂ d₂ n₂/d₂ =
  gcdReduce   d₁ d₂                   λ d₁′ d₂′ g eq₁ eq₂ d₁′/d₂′ →
  gcdReduce-r (n₁ * d₂′ + n₂ * d₁′) g λ s′ g′ g₁ eqs eqg s′/g′ →
  let instance _ = mul-nonzero d₁′ d₂′
               _ = mul-nonzero (d₁′ * d₂′) g′
  in ratio s′ (d₁′ * d₂′ * g′) $
     let[ _ := lemma s′ n₁ d₁ n₂ d₂ d₁′ d₂′ g g₁ eqs  eq₁ n₁/d₁ d₁′/d₂′ ]
     let[ _ := lemma s′ n₂ d₂ n₁ d₁ d₂′ d₁′ g g₁ (by eqs) eq₂ n₂/d₂ auto-coprime ]
     auto-coprime
  where
    lemma : ∀ s′ n₁ d₁ n₂ d₂ d₁′ d₂′ g g₁ →
              s′ * g₁ ≡ n₁ * d₂′ + n₂ * d₁′ →
              d₁′ * g ≡ d₁ →
              Coprime n₁ d₁ → Coprime d₁′ d₂′ → Coprime s′ d₁′
    lemma s′ n₁ d₁ n₂ d₂ d₁′ d₂′ g g₁ eqs refl n₁/d₁ d₁′/d₂′ =
      coprimeByPrimes s′ d₁′ λ p isP p|s′ p|d₁′ →
          let p|n₁d₂′ : p Divides (n₁ * d₂′)
              p|n₁d₂′ = divides-sub-r {n₁ * d₂′} {n₂ * d₁′}
                          (transport (p Divides_) eqs (divides-mul-l g₁ p|s′))
                          (divides-mul-r n₂ p|d₁′)
              p|d₁ : p Divides d₁
              p|d₁ = divides-mul-l g p|d₁′
              p/n₁ : Coprime p n₁
              p/n₁ = case prime-coprime/divide p n₁ isP of λ where
                       (left p/n₁)  → p/n₁
                       (right p|n₁) → ⊥-elim (prime-divide-coprime p n₁ d₁ isP n₁/d₁ p|n₁ p|d₁)
              p|d₂′ : p Divides d₂′
              p|d₂′ = coprime-divide-mul-l p n₁ d₂′ p/n₁ p|n₁d₂′
          in divide-coprime p d₁′ d₂′ d₁′/d₂′ p|d₁′ p|d₂′

-- Specification for addition
slowAddQ : Rational → Rational → Rational
slowAddQ (ratio p q _) (ratio p₁ q₁ _) =
  mkratio (p * q₁ + p₁ * q) (q * q₁) ⦃ mul-nonzero q q₁ ⦄

_-Q_ : Rational → Rational → Rational
ratio p q _ -Q ratio p₁ q₁ _ =
  mkratio (p * q₁ - p₁ * q) (q * q₁) ⦃ mul-nonzero q q₁ ⦄

-- Fast multiplication based on the same technique as the fast addition, except it's much
-- simpler for multiplication.
_*Q_ : Rational → Rational → Rational
ratio n₁ d₁ _ *Q ratio n₂ d₂ _ =
  gcdReduce-r n₁ d₂ λ n₁′ d₂′ g₁ n₁′g₁=n₁ d₂′g₁=d₂ _ →
  gcdReduce-r n₂ d₁ λ n₂′ d₁′ g₂ n₂′g₂=n₂ d₁′g₂=d₁ _ →
  let instance _ = mul-nonzero d₁′ d₂′ in
  ratio (n₁′ * n₂′) (d₁′ * d₂′) $
    case₄ n₁′g₁=n₁ , d₂′g₁=d₂ , n₂′g₂=n₂ , d₁′g₂=d₁ of λ where
      refl refl refl refl → auto-coprime

-- Specification for multiplication
slowMulQ : Rational → Rational → Rational
slowMulQ (ratio p q _) (ratio p₁ q₁ _) = mkratio (p * p₁) (q * q₁) {{mul-nonzero q q₁}}

recip : (x : Rational) {{_ : NonZeroQ x}} → Rational
recip (ratio 0 q eq) {{}}
recip (ratio (suc p) q eq) = ratio q (suc p) auto-coprime

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
  Number.Constraint NumberRational _ = ⊤
  fromNat {{NumberRational}} n = n :/ 1

  SemiringRational : Semiring Rational
  zro {{SemiringRational}} = 0 :/ 1
  one {{SemiringRational}} = 1 :/ 1
  _+_ {{SemiringRational}} = _+Q_
  _*_ {{SemiringRational}} = _*Q_

  ShowRational : Show Rational
  showsPrec {{ShowRational}} _ (ratio p 1 _) = shows p
  showsPrec {{ShowRational}} _ (ratio p q _) = shows p ∘ showString "/" ∘ shows q

-- Ordering --

private
  module _ {p q eq p₁ q₁ eq₁} {{_ : NonZero q}} {{_ : NonZero q₁}} where
    ratio-inj₁ : ratio p q eq ≡ ratio p₁ q₁ eq₁ → p ≡ p₁
    ratio-inj₁ refl = refl

    ratio-inj₂ : ratio p q eq ≡ ratio p₁ q₁ eq₁ → q ≡ q₁
    ratio-inj₂ refl = refl

cong-ratio : ∀ {p q eq p₁ q₁ eq₁} {nzq : NonZero q} {nzq₁ : NonZero q₁} →
             p ≡ p₁ → q ≡ q₁ → ratio p q ⦃ nzq ⦄ eq ≡ ratio p₁ q₁ ⦃ nzq₁ ⦄ eq₁
cong-ratio {q = zero} {nzq = ()}
cong-ratio {q = suc q} refl refl = ratio _ _ $≡ smashed

instance
  EqRational : Eq Rational
  _==_ {{EqRational}} (ratio p q prf) (ratio p₁ q₁ prf₁) with p == p₁ | q == q₁
  ... | no p≠p₁  | _        = no (p≠p₁ ∘ ratio-inj₁)
  ... | yes _    | no q≠q₁  = no (q≠q₁ ∘ ratio-inj₂)
  ... | yes p=p₁ | yes q=q₁ = yes (cong-ratio p=p₁ q=q₁)

data LessQ (x y : Rational) : Set where
  lessQ : numerator x * denominator y < numerator y * denominator x → LessQ x y

private
  lem-unique : ∀ n₁ d₁ n₂ d₂ ⦃ _ : NonZero d₁ ⦄ ⦃ _ : NonZero d₂ ⦄ →
                 Coprime n₁ d₁ → Coprime n₂ d₂ →
                 n₁ * d₂ ≡ n₂ * d₁ → n₁ ≡ n₂ × d₁ ≡ d₂
  lem-unique n₁ d₁ n₂ d₂ n₁⊥d₁ n₂⊥d₂ eq =
    let n₁|n₂ : n₁ Divides n₂
        n₁|n₂ = coprime-divide-mul-r n₁ n₂ d₁ n₁⊥d₁ (factor d₂ (by eq))
        n₂|n₁ : n₂ Divides n₁
        n₂|n₁ = coprime-divide-mul-r n₂ n₁ d₂ n₂⊥d₂ (factor d₁ (by eq))
        d₁|d₂ : d₁ Divides d₂
        d₁|d₂ = coprime-divide-mul-r d₁ d₂ n₁ auto-coprime (factor n₂ (by eq))
        d₂|d₁ : d₂ Divides d₁
        d₂|d₁ = coprime-divide-mul-r d₂ d₁ n₂ auto-coprime (factor n₁ (by eq))
    in divides-antisym n₁|n₂ n₂|n₁ , divides-antisym d₁|d₂ d₂|d₁

compareQ : ∀ x y → Comparison LessQ x y
compareQ (ratio n₁ d₁ n₁⊥d₁) (ratio n₂ d₂ n₂⊥d₂) =
  case compare (n₁ * d₂) (n₂ * d₁) of λ where
    (less lt)    → less (lessQ lt)
    (equal eq)   → equal (uncurry cong-ratio (lem-unique n₁ d₁ n₂ d₂ n₁⊥d₁ n₂⊥d₂ eq))
    (greater gt) → greater (lessQ gt)

instance
  OrdQ : Ord Rational
  OrdQ = defaultOrd compareQ
