-- A certified implementation of the extended Euclidian algorithm,
-- which in addition to the gcd also computes the coefficients of
-- Bézout's identity. That is, integers x and y, such that
-- ax + by = gcd a b.

-- See https://en.wikipedia.org/wiki/Extended_Euclidean_algorithm
-- for details.

module Numeric.Nat.GCD.Extended where

open import Prelude
open import Control.WellFounded
open import Numeric.Nat.Divide
open import Numeric.Nat.DivMod
open import Numeric.Nat.GCD
open import Tactic.Nat

-- Bézout coefficients always have opposite signs, so we can represent
-- a Bézout identity using only natural numbers, keeping track of which
-- coefficient is the positive one.
data BézoutIdentity (d a b : Nat) : Set where
  bézoutL : (x y : Nat) → a * x ≡ d + b * y → BézoutIdentity d a b
  bézoutR : (x y : Nat) → b * y ≡ d + a * x → BézoutIdentity d a b

-- The result of the extended gcd algorithm is the same as for the normal
-- one plus a BézoutIdentity.
record ExtendedGCD (a b : Nat) : Set where
  no-eta-equality
  constructor gcd-res
  field d      : Nat
        isGCD  : IsGCD d a b
        bézout : BézoutIdentity d a b

-- Erasing the proof objects

eraseBézout : ∀ {a b d} → BézoutIdentity d a b → BézoutIdentity d a b
eraseBézout (bézoutL x y eq) = bézoutL x y (eraseEquality eq)
eraseBézout (bézoutR x y eq) = bézoutR x y (eraseEquality eq)

eraseExtendedGCD : ∀ {a b} → ExtendedGCD a b → ExtendedGCD a b
eraseExtendedGCD (gcd-res d p i) = gcd-res d (eraseIsGCD p) (eraseBézout i)

private

  -- The algorithm computes a sequence of coefficients xᵢ and yᵢ (sᵢ and tᵢ on
  -- Wikipedia) that terminates in the Bézout coefficients for a and b. The
  -- invariant is that they satisfy the Bézout identity for the current remainder.
  -- Moreover, at each step they flip sign, so we can represent two consecutive
  -- pairs of coefficients as follows.
  data BézoutState (a b r₀ r₁ : Nat) : Set where
    bézoutLR : ∀ x₀ x₁ y₀ y₁ (eq₀ : a * x₀ ≡ r₀ + b * y₀)
                             (eq₁ : b * y₁ ≡ r₁ + a * x₁) → BézoutState a b r₀ r₁
    bézoutRL : ∀ x₀ x₁ y₀ y₁ (eq₀ : b * y₀ ≡ r₀ + a * x₀)
                             (eq₁ : a * x₁ ≡ r₁ + b * y₁) → BézoutState a b r₀ r₁

  -- In the base case the last remainder is 0, and the second to last is the gcd,
  -- so we get the Bézout coefficients from the first components in the state.
  getBézoutIdentity : ∀ {d a b} → BézoutState a b d 0 → BézoutIdentity d a b
  getBézoutIdentity (bézoutLR x₀ _ y₀ _ eq₀ _) = bézoutL x₀ y₀ eq₀
  getBézoutIdentity (bézoutRL x₀ _ y₀ _ eq₀ _) = bézoutR x₀ y₀ eq₀

  -- It's important for compile time performance to be strict in the computed
  -- coefficients. Can't do a dependent force here due to the proof object. Note
  -- that we only have to be strict in x₁ and y₁, since x₀ and y₀ are simply
  -- the x₁ and y₁ of the previous state.
  forceState : ∀ {a b r₀ r₁} {C : Set} → BézoutState a b r₀ r₁ → (BézoutState a b r₀ r₁ → C) → C
  forceState (bézoutLR x₀ x₁ y₀ y₁ eq₀ eq₁) k =
    force′ x₁ λ x₁′ eqx → force′ y₁ λ y₁′ eqy →
    k (bézoutLR x₀ x₁′ y₀ y₁′ eq₀ (case eqx of λ where refl → case eqy of λ where refl → eq₁))
  forceState (bézoutRL x₀ x₁ y₀ y₁ eq₀ eq₁) k =
    force′ x₁ λ x₁′ eqx → force′ y₁ λ y₁′ eqy →
    k (bézoutRL x₀ x₁′ y₀ y₁′ eq₀ (case eqx of λ where refl → case eqy of λ where refl → eq₁))

  -- We're starting of the algorithm with two first remainders being a and b themselves.
  -- The corresponding coefficients are x₀, x₁ = 1, 0 and y₀, y₁ = 0, 1.
  initialState : ∀ {a b} → BézoutState a b a b
  initialState = bézoutLR 1 0 0 1 auto auto

  module _ {r₀ r₁ r₂} q where
    -- The proof that new coefficients satisfy the invariant.
    -- Note alternating sign: x₀ pos, x₁ neg, x₂ pos.
    lemma : (a b x₀ x₁ y₀ y₁ : Nat) →
            q * r₁ + r₂ ≡ r₀ →
            a * x₀ ≡ r₀ + b * y₀ →
            b * y₁ ≡ r₁ + a * x₁ →
            a * (x₀ + q * x₁) ≡ r₂ + b * (y₀ + q * y₁)
    lemma a b x₀ x₁ y₀ y₁ refl eq₀ eq₁ =
        a * (x₀ + q * x₁)
          ≡⟨ by eq₀ ⟩
        r₂ + b * y₀ + q * (r₁ + a * x₁)
          ≡⟨ (r₂ + b * y₀ +_) ∘ (q *_) $≡ by eq₁ ⟩
        r₂ + b * y₀ + q * (b * y₁)
          ≡⟨ auto ⟩
        r₂ + b * (y₀ + q * y₁) ∎

    -- The sequence of coefficients is defined by
    --   xᵢ₊₁ = xᵢ₋₁ + q * xᵢ
    --   yᵢ₊₁ = yᵢ₋₁ + q * yᵢ
    -- where q is defined by the step in the normal Euclidian algorithm
    --   rᵢ₊₁ = rᵢ₋₁ + q * rᵢ
    bézoutState-step : ∀ {a b} → q * r₁ + r₂ ≡ r₀ → BézoutState a b r₀ r₁ → BézoutState a b r₁ r₂
    bézoutState-step {a} {b} eq (bézoutLR x₀ x₁ y₀ y₁ eq₀ eq₁) =
      bézoutRL x₁ (x₀ + q * x₁) y₁ (y₀ + q * y₁) eq₁ (lemma a b x₀ x₁ y₀ y₁ eq eq₀ eq₁)
    bézoutState-step {a} {b} eq (bézoutRL x₀ x₁ y₀ y₁ eq₀ eq₁) =
      bézoutLR x₁ (x₀ + q * x₁) y₁ (y₀ + q * y₁) eq₁ (lemma b a y₀ y₁ x₀ x₁ eq eq₀ eq₁)

private
  -- This differs slightly from the gcd implementation in Numeric.Nat.GCD where the
  -- recursive call produces a GCD r₁ r₂ that we turn into a GCD r₀ r₁ on the way up.
  -- In the extended algorithm we get Bézout coefficients for the original a and b in
  -- the base case, so instead we push down a function proving IsGCD d a b from
  -- IsGCD d r₀ r₁.
  extendedGCD-acc : {a b : Nat} → (r₀ r₁ : Nat) →
                     (∀ {d} → IsGCD d r₀ r₁ → IsGCD d a b) →
                     BézoutState a b r₀ r₁ →
                     Acc _<_ r₁ → ExtendedGCD a b
  extendedGCD-acc r₀ zero step s _ =
    gcd-res r₀ (step (is-gcd (factor 1 auto) (factor! 0) (λ k p _ → p))) (getBézoutIdentity s)
  extendedGCD-acc r₀ (suc r₁) step s (acc wf) =
    forceState s λ s → -- make sure to be strict in xᵢ and yᵢ
    case r₀ divmod suc r₁ of λ where
      (qr q r₂ lt eq) →
        extendedGCD-acc (suc r₁) r₂ (step ∘ isGCD-step q eq) (bézoutState-step q eq s) (wf r₂ lt)

-- The extended Euclidian algorithm. Compile time performance seems to be quadratic in
-- the number of digits of the inputs, which you start noticing at around ~100 digits.
extendedGCD : (a b : Nat) → ExtendedGCD a b
extendedGCD a b = eraseExtendedGCD (extendedGCD-acc a b id initialState (wfNat b))
