
module Numeric.Nat.LCM where

open import Prelude
open import Numeric.Nat.Divide
open import Numeric.Nat.Divide.Properties
open import Numeric.Nat.GCD
open import Numeric.Nat.GCD.Extended
open import Numeric.Nat.Properties
open import Tactic.Nat

--- Least common multiple ---

record IsLCM m a b : Set where
  no-eta-equality
  constructor is-lcm
  field
    a|m : a Divides m
    b|m : b Divides m
    l   : ∀ k → a Divides k → b Divides k → m Divides k

record LCM a b : Set where
  no-eta-equality
  constructor lcm-res
  field
    m : Nat
    isLCM : IsLCM m a b

open LCM using () renaming (m to get-lcm) public

eraseIsLCM : ∀ {a b m} → IsLCM m a b → IsLCM m a b
eraseIsLCM (is-lcm a|m b|m g) = is-lcm (fast-divides a|m) (fast-divides b|m)
                                       λ k a|k b|k → fast-divides (g k a|k b|k)

eraseLCM : ∀ {a b} → LCM a b → LCM a b
eraseLCM (lcm-res m p) = lcm-res m (eraseIsLCM p)

private
  lem-is-lcm : ∀ {a b d} (g : IsGCD d a b) →
               IsLCM (is-gcd-factor₁ g * b) a b
  lem-is-lcm {a} {b} {0} (is-gcd (factor q eq) d|b g)
             rewrite a ≡⟨ by eq ⟩ 0 ∎ | divides-zero d|b | q * 0 ≡⟨ auto ⟩ 0 ∎ =
    is-lcm divides-refl divides-refl (λ _ 0|k _ → 0|k)
  lem-is-lcm {a} {b} {d@(suc d′)} isg@(is-gcd (factor! q) d|b@(factor! q′) g) =
    is-lcm (divides-mul-cong-l q d|b)
           (divides-mul-r q divides-refl) least
    where
      lem : IsGCD d a b
      lem = is-gcd (factor! q) d|b g

      lem₂ : Coprime q q′
      lem₂ = is-gcd-factors-coprime lem

      least : ∀ k → a Divides k → b Divides k → (q * b) Divides k
      least k (factor qa qa=k) (factor qb qb=k) =
        case lem₄ of λ where
          (factor! qqb) → factor qqb (by qb=k)
        where
          lem₃ : qa * q ≡ q′ * qb
          lem₃ = mul-inj₁ (qa * q) (q′ * qb) (suc d′)
                 (by (qa=k ⟨≡⟩ʳ qb=k))

          lem₄ : q Divides qb
          lem₄ = coprime-divide-mul-l q q′ qb (is-gcd-factors-coprime isg)
                 (factor qa lem₃)

lcm : ∀ a b → LCM a b
lcm a b = eraseLCM $
  case gcd a b of λ where
    (gcd-res d g) →
      lcm-res (is-gcd-factor₁ g * b) (lem-is-lcm g)

lcm! : Nat → Nat → Nat
lcm! a b = get-lcm (lcm a b)

--- Properties ---

is-lcm-unique : ∀ {m m₁ a b} → IsLCM m a b → IsLCM m₁ a b → m ≡ m₁
is-lcm-unique {m} {m₁} (is-lcm a|m b|m lm) (is-lcm a|m₁ b|m₁ lm₁) =
  divides-antisym (lm m₁ a|m₁ b|m₁) (lm₁ m a|m b|m)

lcm-unique : ∀ {m a b} → IsLCM m a b → lcm! a b ≡ m
lcm-unique {a = a} {b} lm with lcm a b
... | lcm-res m₁ lm₁ = is-lcm-unique lm₁ lm

is-lcm-commute : ∀ {m a b} → IsLCM m a b → IsLCM m b a
is-lcm-commute (is-lcm a|m b|m g) = is-lcm b|m a|m (flip ∘ g)

lcm-commute : ∀ {a b} → lcm! a b ≡ lcm! b a
lcm-commute {a} {b} with lcm b a
... | lcm-res m lm = lcm-unique (is-lcm-commute lm)

private
  _|>_ = divides-trans

lcm-assoc : ∀ a b c → lcm! a (lcm! b c) ≡ lcm! (lcm! a b) c
lcm-assoc a b c with lcm a b | lcm b c
... | lcm-res ab (is-lcm a|ab b|ab lab)
    | lcm-res bc (is-lcm b|bc c|bc lbc) with lcm ab c
...    | lcm-res ab-c (is-lcm ab|abc c|abc labc) =
  lcm-unique {ab-c} {a} {bc}
    (is-lcm (a|ab |> ab|abc)
            (lbc ab-c (b|ab |> ab|abc) c|abc)
            λ k a|k bc|k → labc k (lab k a|k (b|bc |> bc|k)) (c|bc |> bc|k))
