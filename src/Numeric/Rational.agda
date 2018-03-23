
module Numeric.Rational where

open import Prelude
open import Numeric.Nat.GCD
open import Numeric.Nat.GCD.Extended
open import Numeric.Nat.Prime
open import Numeric.Nat.Prime.Properties
open import Numeric.Nat.Divide
open import Numeric.Nat.Properties
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

  mkratio-lem : ∀ p q d p′ q′ {{_ : NonZero q}} →
                p′ * d ≡ p →
                q′ * d ≡ q →
                (∀ k → k Divides p → k Divides q → k Divides d) →
                gcd! p′ q′ ≡ 1
  mkratio-lem p q d p′ q′ eqp eqq g with gcd p′ q′
  mkratio-lem ._ ._ d ._ ._ refl refl g
    | gcd-res d′ (is-gcd (factor! p₂) (factor! q₂) g′) =
    let p′ = p₂ * d′
        q′ = q₂ * d′
        p = p′ * d
        q = q′ * d
        instance
          nzd : NonZero d
          nzd = transport NonZero (gcd-unique p q d (is-gcd (factor! p′) (factor! q′) g)) (nonzero-gcd-r p q)
        dd′|d : (d′ * d) Divides d
        dd′|d = g (d′ * d) (factor p₂ auto) (factor q₂ auto)
    in lem-divide-mul d′ d dd′|d

  lem-nonzero-mul-l : ∀ a b c {{_ : NonZero c}} → a * b ≡ c → NonZero a
  lem-nonzero-mul-l  0      b .0 {{}} refl
  lem-nonzero-mul-l (suc a) b  c eq = _

  lem-nonzero-mul : ∀ a b {{_ : NonZero a}} {{_ : NonZero b}} → NonZero (a * b)
  lem-nonzero-mul zero b {{}}
  lem-nonzero-mul a zero {{_}} {{}}
  lem-nonzero-mul (suc a) (suc b) = _

infixl 7 mkratio
syntax mkratio p q = p :/ q
mkratio : (p q : Nat) {{_ : NonZero q}} → Rational
mkratio p q with gcd p q
... | gcd-res d (is-gcd (factor p′ eq) (factor q′ eq₁) g) =
  ratio p′ q′ {{lem-nonzero-mul-l q′ d q eq₁}} (mkratio-lem p q d p′ q′ eq eq₁ g)

mkratio-sound : (p q : Nat) {{_ : NonZero q}} → p * denominator (mkratio p q) ≡ q * numerator (mkratio p q)
mkratio-sound p q with gcd p q
mkratio-sound ._ ._ | gcd-res d (is-gcd (factor! p′) (factor! q′) _) = auto

NonZeroQ : Rational → Set
NonZeroQ x = NonZero (numerator x)

infixl 6 _+Q_ _-Q_
infixl 7 _*Q_ _/Q_

-- Fast addition of rationals due to Knuth (The Art of Computer Programming, volume 2).
-- Proof sketch by Sergei Meshveliani.
-- n₁ / d₁ + n₂ / d₂ = s′ / (d₁′ * d₂′ * g′)
--   where
--     g = gcd d₁ d₂ ⌉
--     d₁′ = d₁ / g   > computed by gcdReduce
--     d₂′ = d₂ / g  ⌋
--     s   = n₁ * d₂′ + n₂ * d₁′
--     g₁  = gcd s g ⌉
--     s′  = s / g₁   > second gcdReduce
--     g′  = g / g₁  ⌋
fastAddQ : Rational → Rational → Rational
fastAddQ (ratio n₁ d₁ n₁/d₁) (ratio n₂ d₂ n₂/d₂) =
  gcdReduce d₁ d₂                   λ d₁′ d₂′ g nzd₁ eq₁ eq₂ d₁′/d₂′ →
  gcdReduce (n₁ * d₂′ + n₂ * d₁′) g λ s′ g′ g₁ _ eqs eqg s′/g′ →
  let instance _ = nzd₁ in
  ratio s′ (d₁′ * d₂′ * g′)
    ⦃ mul-nonzero (d₁′ * d₂′) g′ ⦃ mul-nonzero d₁′ _ ⦄ ⦄
    (coprime-mul s′ (d₁′ * d₂′) g′
      (coprime-mul s′ d₁′ d₂′
        (lemma s′ n₁ d₁ n₂ d₂ d₁′ d₂′ g g₁ eqs eq₁ n₁/d₁ d₁′/d₂′)
        (lemma s′ n₂ d₂ n₁ d₁ d₂′ d₁′ g g₁ (eqs ⟨≡⟩ add-commute (n₁ * d₂′) _)
               eq₂ n₂/d₂ (coprime-sym d₁′ d₂′ d₁′/d₂′)))
      s′/g′)
  where
    lemma : ∀ s′ n₁ d₁ n₂ d₂ d₁′ d₂′ g g₁ →
              s′ * g₁ ≡ n₁ * d₂′ + n₂ * d₁′ →
              d₁′ * g ≡ d₁ →
              Coprime n₁ d₁ → Coprime d₁′ d₂′ → Coprime s′ d₁′
    lemma s′ n₁ d₁ n₂ d₂ d₁′ d₂′ g g₁ eqs eq₁ n₁/d₁ d₁′/d₂′ =
      coprimeByPrimes s′ d₁′ λ p isP p|s′ p|d₁′ →
          let p|n₁d₂′ : p Divides (n₁ * d₂′)
              p|n₁d₂′ = divides-sub-r {n₁ * d₂′} {n₂ * d₁′}
                          (transport (p Divides_) eqs (divides-mul-l g₁ p|s′))
                          (divides-mul-r n₂ p|d₁′)
              p|d₁ : p Divides d₁
              p|d₁ = transport (p Divides_) eq₁ (divides-mul-l g p|d₁′)
              p/n₁ : Coprime p n₁
              p/n₁ = case prime-coprime/divide p n₁ isP of λ where
                       (left p/n₁)  → p/n₁
                       (right p|n₁) → ⊥-elim (prime-divide-coprime p n₁ d₁ isP n₁/d₁ p|n₁ p|d₁)
              p|d₂′ : p Divides d₂′
              p|d₂′ = coprime-divide-mul-l p n₁ d₂′ p/n₁ p|n₁d₂′
          in divide-coprime p d₁′ d₂′ d₁′/d₂′ p|d₁′ p|d₂′

slowAddQ : Rational → Rational → Rational
slowAddQ (ratio p q _) (ratio p₁ q₁ _) = mkratio (p * q₁ + p₁ * q) (q * q₁) {{lem-nonzero-mul q q₁}}

_+Q_ : Rational → Rational → Rational
_+Q_ = fastAddQ

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

  lem : ∀ {p q eq p₁ q₁ eq₁} {{_ : NonZero q}} {{_ : NonZero q₁}} →
          p ≡ p₁ → q ≡ q₁ → ratio p q eq ≡ ratio p₁ q₁ eq₁
  lem {q = zero} {{}}
  lem {q = suc q} refl refl = ratio _ _ $≡ smashed

instance
  EqRational : Eq Rational
  _==_ {{EqRational}} (ratio p q prf) (ratio p₁ q₁ prf₁) with p == p₁ | q == q₁
  ... | no p≠p₁  | _        = no (p≠p₁ ∘ ratio-inj₁)
  ... | yes _    | no q≠q₁  = no (q≠q₁ ∘ ratio-inj₂)
  ... | yes p=p₁ | yes q=q₁ = yes (lem p=p₁ q=q₁)
