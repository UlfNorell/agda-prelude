
-- Integers modulo N
module Data.Nat.Modulo where

open import Prelude
open import Data.Nat.DivMod
open import Control.Strict
open import Tactic.Nat

data IntMod (n : Nat) : Set where
  modn : ∀ k → k < n → IntMod n

{-# DISPLAY modn k (diff _ refl) = k #-}

negIntMod : ∀ {n} → IntMod n → IntMod n
negIntMod (modn 0 lt) = modn 0 lt
negIntMod (modn (suc k) (diff j eq)) = modn (suc j) (by (sym eq))

{-# DISPLAY negIntMod a = negate a #-}

private
  toMod : ∀ {n} → Nat → IntMod (suc n)
  toMod {n} k with k divmod suc n
  toMod k | qr _ r lt _ = modn r lt

instance
  NumberIntMod : ∀ {n} → Number (IntMod (suc n))
  NumberIntMod {n} = record { Constraint = λ _ → ⊤ ; fromNat = λ k → toMod k }

  NegativeIntMod : ∀ {n} → Negative (IntMod (suc n))
  NegativeIntMod {n} = record { Constraint = λ _ → ⊤ ; fromNeg = λ k → negIntMod (fromNat k) }

addIntMod : ∀ {n} → IntMod (suc n) → IntMod (suc n) → IntMod (suc n)
addIntMod {n} (modn a _) (modn b _) = force (a + b) λ a+b → fromNat a+b ofType IntMod (suc n)

mulIntMod : ∀ {n} → IntMod (suc n) → IntMod (suc n) → IntMod (suc n)
mulIntMod {n} (modn a _) (modn b _) = force (a * b) λ a*b → fromNat a*b ofType IntMod (suc n)

subIntMod : ∀ {n} → IntMod (suc n) → IntMod (suc n) → IntMod (suc n)
subIntMod a b = addIntMod a (negIntMod b)

{-# DISPLAY addIntMod a b = a + b #-}
{-# DISPLAY mulIntMod a b = a * b #-}
{-# DISPLAY subIntMod a b = a - b #-}

instance
  SemiringIntMod : ∀ {n} → Semiring (IntMod (suc n))
  SemiringIntMod = record { zro = 0 ; one = 1 ; _+_ = addIntMod ; _*_ = mulIntMod }

  SubtractiveIntMod : ∀ {n} → Subtractive (IntMod (suc n))
  SubtractiveIntMod {n} = record { _-_ = subIntMod ; negate = negIntMod }

  unquoteDecl ForceIntMod = deriveForceable (quote IntMod)
