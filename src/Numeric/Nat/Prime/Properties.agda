
module Numeric.Nat.Prime.Properties where

open import Prelude
open import Control.WellFounded
open import Numeric.Nat.Properties
open import Numeric.Nat.Divide
open import Numeric.Nat.Divide.Properties
open import Numeric.Nat.GCD
open import Numeric.Nat.GCD.Extended
open import Numeric.Nat.GCD.Properties
open import Numeric.Nat.Prime
open import Tactic.Nat

prime-coprime/divide : ∀ p a → Prime p → Either (Coprime p a) (p Divides a)
prime-coprime/divide p a (prime _ isp) with gcd p a
prime-coprime/divide p a (prime _ isp) | gcd-res d isGCD =
  case isp d (IsGCD.d|a isGCD) of λ where
    (left d=1)   → left  d=1
    (right refl) → right (IsGCD.d|b isGCD)

prime-split : ∀ {p} a b → Prime p → p Divides (a * b) → Either (p Divides a) (p Divides b)
prime-split a b isP p|ab =
  case prime-coprime/divide _ a isP of λ where
    (left p/a)  → right (coprime-divide-mul-l _ a b p/a p|ab)
    (right p|a) → left p|a

private
  -- Used for the well-founded induction over factorisation in coprimeByPrimes.
  lem-l : (a b : Nat) → a > 1 → b > 1 → a < a * b
  lem-l a b (diff! k) (diff! j) = auto

  lem-r : (a b : Nat) → a > 1 → b > 1 → b < a * b
  lem-r a b (diff! k) (diff! j) = auto

divides1-equals1 : ∀ {a} → a Divides 1 → a ≡ 1
divides1-equals1         (factor zero ())
divides1-equals1         (factor (suc zero) eq) = by eq
divides1-equals1 {zero}  (factor (suc (suc q)) eq) = refute eq
divides1-equals1 {suc a} (factor (suc (suc q)) eq) = refute eq

-- It's enough to check prime divisors when checking coprimality.
module _ (a b : Nat) (f : ∀ p → Prime p → p Divides a → p Divides b → p Divides 1) where

  private
    coprimeByPrimes′ : (k : Nat) → Acc _<_ k → k Divides a → k Divides b → k Divides 1
    coprimeByPrimes′ k (acc wf) k|a k|b =
      case isPrime k of λ where
        (yes isP) → f k isP k|a k|b
        (no (composite i j i>1 j>1 refl)) →
          let i|1 : i Divides 1
              i|1 = coprimeByPrimes′ i (wf i (lem-l i j i>1 j>1))
                                       (mul-divides-l i j a k|a) (mul-divides-l i j b k|b)
              j|1 : j Divides 1
              j|1 = coprimeByPrimes′ j (wf j (lem-r i j i>1 j>1))
                                       (mul-divides-r i j a k|a) (mul-divides-r i j b k|b)
          in case₂ divides1-equals1 i|1 , divides1-equals1 j|1 of λ where
               refl refl → factor! 1
        (tiny (diff! 0)) → factor! 1
        (tiny (diff! 1)) →
          case₂ divides-zero k|a , divides-zero k|b of λ where
            refl refl →
              let 2∤1 = fromDec (2 divides? 1)
                  2|0 = fromDec (2 divides? 0) in
              ⊥-elim (2∤1 (f 2 (fromDec (decPrime 2)) 2|0 2|0))
        (tiny (diff (suc (suc _)) eq)) → refute eq

  coprimeByPrimes : Coprime a b
  coprimeByPrimes = coprimeByDivide a b λ k → coprimeByPrimes′ k (wfNat k)

coprime-mul : ∀ a b c → Coprime a b → Coprime a c → Coprime a (b * c)
coprime-mul a b c a/b a/c =
  coprimeByPrimes a (b * c) λ p isP p|a p|bc →
  case prime-split b c isP p|bc of λ where
    (left  p|b) → divide-coprime p a b a/b p|a p|b
    (right p|c) → divide-coprime p a c a/c p|a p|c

prime-divide-coprime : ∀ p a b → Prime p → Coprime a b → p Divides a → p Divides b → ⊥
prime-divide-coprime p a b isP a/b p|a p|b =
  case divides1-equals1 {p} (divide-coprime p a b a/b p|a p|b) of λ where
    refl → fromDec (decPrime 1) isP
