
module Numeric.Nat.GCD where

open import Prelude
open import Control.WellFounded
open import Numeric.Nat.Properties
open import Numeric.Nat.DivMod
open import Numeric.Nat.Divide
open import Tactic.Nat

--- GCD ---

record IsGCD (d a b : Nat) : Set where
  no-eta-equality
  constructor is-gcd
  field d|a : d Divides a
        d|b : d Divides b
        g   : ∀ k → k Divides a → k Divides b → k Divides d

record GCD (a b : Nat) : Set where
  no-eta-equality
  constructor gcd-res
  field d     : Nat
        isGCD : IsGCD d a b

open GCD public using () renaming (d to get-gcd)

-- Projections --

is-gcd-factor₁ : ∀ {a b d} → IsGCD d a b → Nat
is-gcd-factor₁ g = get-factor (IsGCD.d|a g)

is-gcd-factor₂ : ∀ {a b d} → IsGCD d a b → Nat
is-gcd-factor₂ g = get-factor (IsGCD.d|b g)

gcd-factor₁ : ∀ {a b} → GCD a b → Nat
gcd-factor₁ g = is-gcd-factor₁ (GCD.isGCD g)

gcd-factor₂ : ∀ {a b} → GCD a b → Nat
gcd-factor₂ g = is-gcd-factor₂ (GCD.isGCD g)

-- Euclid's algorithm --

isGCD-step : ∀ {d r₀ r₁ r₂} q → q * r₁ + r₂ ≡ r₀ → IsGCD d r₁ r₂ → IsGCD d r₀ r₁
isGCD-step q refl (is-gcd d|r₁ d|r₂ g) =
  is-gcd (divides-add (divides-mul-r q d|r₁) d|r₂)
         d|r₁ (λ k k|r₀ k|r₁ → g k k|r₁ (divides-sub-l k|r₀ (divides-mul-r q k|r₁)))

private
  gcd-step : ∀ {a b} q {r} → q * suc b + r ≡ a → GCD (suc b) r → GCD a (suc b)
  gcd-step q eq (gcd-res d p) = gcd-res d (isGCD-step q eq p)

  gcd-cert-acc : ∀ a b → Acc _<_ b → GCD a b
  gcd-cert-acc a zero _ = gcd-res a (is-gcd (factor 1 auto) (factor! 0) (λ k k|a _ → k|a))
  gcd-cert-acc a (suc b) (acc wf) =
    case a divmod suc b of λ
    { (qr q r lt eq) → gcd-step q eq (gcd-cert-acc (suc b) r (wf r lt)) }

eraseIsGCD : ∀ {d a b} → IsGCD d a b → IsGCD d a b
eraseIsGCD (is-gcd d|a d|b g) =
  is-gcd (fast-divides d|a) (fast-divides d|b)
         λ k k|a k|b → fast-divides (g k k|a k|b)

eraseGCD : ∀ {a b} → GCD a b → GCD a b
eraseGCD (gcd-res d p) = gcd-res d (eraseIsGCD p)

gcd : ∀ a b → GCD a b
gcd 0 b = gcd-res b (is-gcd (factor! 0) divides-refl (λ _ _ k|b → k|b))
gcd 1 b = gcd-res 1 (is-gcd divides-refl (factor b auto) (λ _ k|1 _ → k|1))
gcd a b = eraseGCD (gcd-cert-acc a b (wfNat b))

gcd! : Nat → Nat → Nat
gcd! a b = get-gcd (gcd a b)

Coprime : Nat → Nat → Set
Coprime a b = gcd! a b ≡ 1

--- Properties ---

gcd-divides-l : ∀ a b → gcd! a b Divides a
gcd-divides-l a b with gcd a b
... | gcd-res _ i = IsGCD.d|a i

gcd-divides-r : ∀ a b → gcd! a b Divides b
gcd-divides-r a b with gcd a b
... | gcd-res _ i = IsGCD.d|b i

is-gcd-unique : ∀ {a b} d₁ d₂ (g₁ : IsGCD d₁ a b) (g₂ : IsGCD d₂ a b) → d₁ ≡ d₂
is-gcd-unique d d′ (is-gcd d|a d|b gd) (is-gcd d′|a d′|b gd′) =
  divides-antisym (gd′ d d|a d|b)
                  (gd  d′ d′|a d′|b)

gcd-unique : ∀ a b d → IsGCD d a b → gcd! a b ≡ d
gcd-unique a b d pd with gcd a b
... | gcd-res d′ pd′ = is-gcd-unique d′ d pd′ pd

is-gcd-commute : ∀ {d a b} → IsGCD d a b → IsGCD d b a
is-gcd-commute (is-gcd d|a d|b g) = is-gcd d|b d|a (flip ∘ g)

gcd-commute : ∀ a b → gcd! a b ≡ gcd! b a
gcd-commute a b with gcd b a
gcd-commute a b | gcd-res d p = gcd-unique a b d (is-gcd-commute p)

gcd-factor-l : ∀ {a b} → a Divides b → gcd! a b ≡ a
gcd-factor-l {a} (factor! b) =
  gcd-unique a (b * a) a
             (is-gcd divides-refl (divides-mul-r b divides-refl) λ _ k|a _ → k|a)

gcd-factor-r : ∀ {a b} → b Divides a → gcd! a b ≡ b
gcd-factor-r {a} {b} b|a = gcd-commute a b ⟨≡⟩ gcd-factor-l b|a

gcd-idem : ∀ a → gcd! a a ≡ a
gcd-idem a = gcd-factor-l divides-refl

gcd-zero-l : ∀ n → gcd! 0 n ≡ n
gcd-zero-l n = gcd-unique 0 n n (is-gcd (factor! 0) divides-refl λ _ _ k|n → k|n)

gcd-zero-r : ∀ n → gcd! n 0 ≡ n
gcd-zero-r n = gcd-commute n 0 ⟨≡⟩ gcd-zero-l n

zero-is-gcd-l : ∀ {a b} → IsGCD 0 a b → a ≡ 0
zero-is-gcd-l (is-gcd 0|a _ _) = divides-zero 0|a

zero-is-gcd-r : ∀ {a b} → IsGCD 0 a b → b ≡ 0
zero-is-gcd-r (is-gcd _ 0|b _) = divides-zero 0|b

zero-gcd-l : ∀ a b → gcd! a b ≡ 0 → a ≡ 0
zero-gcd-l a b eq with gcd a b
zero-gcd-l a b refl | gcd-res .0 p = zero-is-gcd-l p

zero-gcd-r : ∀ a b → gcd! a b ≡ 0 → b ≡ 0
zero-gcd-r a b eq with gcd a b
zero-gcd-r a b refl | gcd-res .0 p = zero-is-gcd-r p

nonzero-gcd-l : ∀ a b {{_ : NonZero a}} → NonZero (gcd! a b)
nonzero-gcd-l 0 _ {{}}
nonzero-gcd-l a@(suc a′) b with gcd a b
... | gcd-res (suc _) _ = _
... | gcd-res 0 (is-gcd (factor q eq) _ _) = refute eq

nonzero-gcd-r : ∀ a b {{_ : NonZero b}} → NonZero (gcd! a b)
nonzero-gcd-r a b = transport NonZero (gcd-commute b a) (nonzero-gcd-l b a)

private
  _|>_ = divides-trans

gcd-assoc : ∀ a b c → gcd! a (gcd! b c) ≡ gcd! (gcd! a b) c
gcd-assoc a b c with gcd a b | gcd b c
... | gcd-res ab (is-gcd ab|a ab|b gab)
    | gcd-res bc (is-gcd bc|b bc|c gbc) with gcd ab c
...    | gcd-res ab-c (is-gcd abc|ab abc|c gabc) =
  gcd-unique a bc ab-c
             (is-gcd (abc|ab |> ab|a)
                     (gbc ab-c (abc|ab |> ab|b) abc|c)
                     λ k k|a k|bc → gabc k (gab k k|a (k|bc |> bc|b))
                                           (k|bc |> bc|c))

coprime-sym : ∀ a b → Coprime a b → Coprime b a
coprime-sym a b p = gcd-commute b a ⟨≡⟩ p

mkcoprime : ∀ a b → (∀ k → k Divides a → k Divides b → k Divides 1) → Coprime a b
mkcoprime a b g = gcd-unique a b 1 (is-gcd one-divides one-divides g)

divide-coprime : ∀ d a b → Coprime a b → d Divides a → d Divides b → d Divides 1
divide-coprime d a b p d|a d|b with gcd a b
divide-coprime d a b refl d|a d|b | gcd-res _ (is-gcd _ _ g) =
  g d d|a d|b

is-gcd-factors-coprime : ∀ {a b d} (p : IsGCD d a b) {{_ : NonZero d}} →
                           Coprime (is-gcd-factor₁ p) (is-gcd-factor₂ p)
is-gcd-factors-coprime {a} {b} {0} _ {{}}
is-gcd-factors-coprime {a} {b} {d@(suc _)} p@(is-gcd (factor qa refl) (factor qb refl) g) with gcd qa qb
... | gcd-res j (is-gcd j|qa j|qb gj) = lem₃ j lem₂
  where
    lem : IsGCD (j * d) a b
    lem = is-gcd (divides-mul-cong-r d j|qa) (divides-mul-cong-r d j|qb) λ k k|a k|b →
                 divides-mul-r j (g k k|a k|b)

    lem₂ : d ≡ j * d
    lem₂ = is-gcd-unique d (j * d) p lem

    lem₃ : ∀ j → d ≡ j * d → j ≡ 1
    lem₃ 0 ()
    lem₃ 1 _ = refl
    lem₃ (suc (suc n)) eq = refute eq
