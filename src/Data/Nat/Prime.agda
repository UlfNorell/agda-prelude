
module Data.Nat.Prime where

open import Prelude
open import Data.Nat.GCD
open import Data.Nat.Divide
open import Data.Nat.DivMod
open import Data.Nat.Properties
open import Tactic.Nat

Coprime : Nat → Nat → Set
Coprime a b = gcd! a b ≡ 1

data Prime n : Set where
  prime : LessThan 1 n → (∀ k → LessThan (suc k) n → Coprime (suc k) n) → Prime n

private
  lem : ∀ a b → LessNat 1 b → LessNat (suc a) (a * b + b)
  lem a .(suc (k + 1)) (diff! k) = diff (a + k + a * k) (tactic auto)

composite-not-prime : ∀ a b → LessThan 1 a → LessThan 1 b → ¬ Prime (a * b)
composite-not-prime  zero   b (diff _ ())
composite-not-prime (suc a) b a>1 b>1 (prime _ f) =
  let 1=sa : 1 ≡ suc a
      1=sa = f a (lem a b b>1) ʳ⟨≡⟩ gcd-mul-l (suc a) b
  in less-antirefl a>1 1=sa
