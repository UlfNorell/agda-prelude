
-- Integers modulo N
module Numeric.Nat.Modulo where

open import Prelude
open import Numeric.Nat.DivMod
open import Tactic.Nat

data IntMod (n : Nat) : Set where
  modn : ∀ k → k < n → IntMod n

{-# DISPLAY modn k (LessNat.diff _ refl) = k #-}

negIntMod : ∀ {n} → IntMod n → IntMod n
negIntMod (modn 0 lt) = modn 0 lt
negIntMod (modn (suc k) (diff j eq)) = modn (suc j) (by (sym eq))

{-# DISPLAY negIntMod a = negate a #-}

instance
  NumberIntMod : ∀ {n} → Number (IntMod (suc n))
  Number.Constraint NumberIntMod _ = ⊤
  fromNat {{NumberIntMod {n}}} k with k divmod suc n
  ... | qr _ r lt _ = modn r lt

  NegativeIntMod : ∀ {n} → Negative (IntMod (suc n))
  Negative.Constraint NegativeIntMod _ = ⊤
  fromNeg {{NegativeIntMod}} k = negIntMod (fromNat k)

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
  zro {{SemiringIntMod}} = 0
  one {{SemiringIntMod}} = 1
  _+_ {{SemiringIntMod}} = addIntMod
  _*_ {{SemiringIntMod}} = mulIntMod

  SubtractiveIntMod : ∀ {n} → Subtractive (IntMod (suc n))
  _-_    {{SubtractiveIntMod}} = subIntMod
  negate {{SubtractiveIntMod}} = negIntMod
