
module Numeric.Rational.Properties where

open import Prelude
open import Numeric.Rational
open import Numeric.Nat.Properties
open import Numeric.Nat.Divide
open import Numeric.Nat.Divide.Properties
open import Numeric.Nat.Prime
open import Numeric.Nat.Prime.Properties
open import Numeric.Nat.GCD
open import Numeric.Nat.GCD.Properties
open import Tactic.Nat
open import Tactic.Nat.Coprime

-- Correctness proof of the Knuth algorithm for addition ----------

private
  lem-coprime : ∀ n₁ n₂ s′ d₁′ d₂′ g g₁ →
                  s′ * g₁ ≡ n₁ * d₂′ + n₂ * d₁′ →
                  Coprime n₁ (d₁′ * g) →
                  Coprime d₁′ d₂′ →
                  Coprime s′ d₁′
  lem-coprime n₁ n₂ s′ d₁′ d₂′ g g₁ s′g₁=s n₁⊥d₁ d₁′⊥d₂′ =
    coprimeByPrimes s′ d₁′ λ p isP p|s′ p|d₁′ →

      let s  = n₁ * d₂′ + n₂ * d₁′
          d₁ = d₁′ * g

          p|d₁ : p Divides d₁
          p|d₁ = divides-mul-l g p|d₁′

          p|s : p Divides s
          p|s = transport (p Divides_) s′g₁=s (divides-mul-l g₁ p|s′)

          p|n₁d₂′ : p Divides (n₁ * d₂′)
          p|n₁d₂′ = divides-sub-r p|s (divides-mul-r n₂ p|d₁′)

          p∤n₁ : ¬ (p Divides n₁)
          p∤n₁ p|n₁ = prime-divide-coprime p n₁ d₁ isP n₁⊥d₁ p|n₁ p|d₁

          p|d₂′ : p Divides d₂′
          p|d₂′ = case prime-split n₁ d₂′ isP p|n₁d₂′ of λ where
                    (left p|n₁)   → ⊥-elim (p∤n₁ p|n₁)
                    (right p|d₂′) → p|d₂′

      in divide-coprime p d₁′ d₂′ d₁′⊥d₂′ p|d₁′ p|d₂′

addQ-sound : ∀ x y → x + y ≡ slowAddQ x y
addQ-sound (ratio n₁ d₁ n₁⊥d₁) (ratio n₂ d₂ n₂⊥d₂)
  with gcd (n₁ * d₂ + n₂ * d₁) (d₁ * d₂) | gcd d₁ d₂
...  | gcd-res g₀ g₀-gcd@(is-gcd (factor p pg₀=n₀) (factor q qg₀=d₀) _)
     | gcd-res g isgcd-dd@(is-gcd (factor! d₁′) (factor! d₂′) _)
  with gcd (n₁ * d₂′ + n₂ * d₁′) g
...  | gcd-res g₁ isgcd-sg@(is-gcd (factor s′ s′g₁=s) (factor! g′) _) =

  let n₀ = n₁ * d₂ + n₂ * d₁
      d₀ = d₁ * d₂
      s  = n₁ * d₂′ + n₂ * d₁′

      instance
        nz-g₀  = nonzero-is-gcd-r ⦃ mul-nonzero d₁ d₂ ⦄ g₀-gcd
        nz-g   = nonzero-is-gcd-l isgcd-dd
        nz-g₁  = nonzero-is-gcd-r isgcd-sg
        nz-gg₁ = mul-nonzero g g₁

      s′gg₁=n₀ : s′ * (g * g₁) ≡ n₀
      s′gg₁=n₀ =
        s′ * (g * g₁)
          ≡⟨ auto ⟩
        s′ * g₁ * g
          ≡⟨ _* g $≡ s′g₁=s ⟩
        (n₁ * d₂′ + n₂ * d₁′) * g
          ≡⟨ auto ⟩
        n₀ ∎

      ddg′gg₁=d₀ : d₁′ * d₂′ * g′ * (g * g₁) ≡ d₀
      ddg′gg₁=d₀ = auto

      s′⊥ddg : Coprime s′ (d₁′ * d₂′ * g′)
      s′⊥ddg =
        let[ _ := is-gcd-factors-coprime isgcd-dd ]
        let[ _ := lem-coprime n₁ n₂ s′ d₁′ d₂′ g g₁ s′g₁=s n₁⊥d₁ auto-coprime ]
        let[ _ := lem-coprime n₂ n₁ s′ d₂′ d₁′ g g₁ (s′g₁=s ⟨≡⟩ auto) n₂⊥d₂ auto-coprime ]
        let[ _ := is-gcd-factors-coprime isgcd-sg ]
        auto-coprime

      gg₁-gcd : IsGCD (g * g₁) n₀ d₀
      gg₁-gcd = is-gcd-by-coprime-factors (g * g₁) n₀ d₀
                  (factor s′ s′gg₁=n₀) (factor (d₁′ * d₂′ * g′) ddg′gg₁=d₀)
                  s′⊥ddg

      gg₁=g₀ : g * g₁ ≡ g₀
      gg₁=g₀ = is-gcd-unique (g * g₁) g₀ gg₁-gcd g₀-gcd

      s′g₀=n₀ : s′ * g₀ ≡ n₀
      s′g₀=n₀ = s′ *_ $≡ sym gg₁=g₀ ⟨≡⟩ s′gg₁=n₀

      ddgg₀=d₀ : d₁′ * d₂′ * g′ * g₀ ≡ d₀
      ddgg₀=d₀ = d₁′ * d₂′ * g′ *_ $≡ sym gg₁=g₀ ⟨≡⟩ ddg′gg₁=d₀

      s′=p : s′ ≡ p
      s′=p = mul-inj₁ s′ p g₀ (s′g₀=n₀ ⟨≡⟩ʳ pg₀=n₀)

      ddg=q : d₁′ * d₂′ * g′ ≡ q
      ddg=q = mul-inj₁ _ q g₀ (ddgg₀=d₀ ⟨≡⟩ʳ qg₀=d₀)

    in cong-ratio s′=p ddg=q
