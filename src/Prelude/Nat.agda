
module Prelude.Nat where

open import Prelude.Unit
open import Prelude.Empty
open import Prelude.Bool
open import Prelude.Decidable
open import Prelude.Equality
open import Prelude.Equality.Unsafe
open import Prelude.Function
open import Prelude.Ord

data Nat : Set where
  zero : Nat
  suc  : (n : Nat) → Nat

{-# BUILTIN NATURAL Nat #-}

--- Addition, subtraction and multiplication ---

infixl 6 _+_ _-_
infixl 7 _*_ natDiv natMod

_+_ : Nat → Nat → Nat
zero  + m = m
suc n + m = suc (n + m)

_-_ : Nat → Nat → Nat
n     - zero = n
zero  - suc m = zero
suc n - suc m = n - m

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATMINUS _-_ #-}

_*_ : Nat → Nat → Nat
zero  * m = zero
suc n * m = n * m + m

{-# BUILTIN NATTIMES _*_ #-}

--- Equality ---

NonZero : Nat → Set
NonZero zero    = ⊥
NonZero (suc _) = ⊤

suc-inj : ∀ {n m} → suc n ≡ suc m → n ≡ m
suc-inj refl = refl

eqNat : Nat → Nat → Bool
eqNat  zero    zero   = true
eqNat (suc n) (suc m) = eqNat n m
eqNat  _       _      = false

{-# BUILTIN NATEQUALS eqNat #-}

private
  eqNatSound : ∀ n m → IsTrue (eqNat n m) → n ≡ m
  eqNatSound zero zero _ = refl
  eqNatSound zero (suc m) ()
  eqNatSound (suc n) zero ()
  eqNatSound (suc n) (suc m) p rewrite eqNatSound n m p = refl

  decEqNat : (n m : Nat) → Dec (n ≡ m)
  decEqNat n m with eqNat n m | eqNatSound n m
  ... | true  | eq = yes (safeEqual (eq _))
  ... | false | _  = no  unsafeNotEqual

EqNat : Eq Nat
EqNat = record { _==_ = decEqNat }

--- Division and modulo ---

private
  divAux : Nat → Nat → Nat → Nat → Nat
  divAux k m  zero    j      = k
  divAux k m (suc n)  zero   = divAux (suc k) m n m
  divAux k m (suc n) (suc j) = divAux k m n j

  {-# BUILTIN NATDIVSUCAUX divAux #-}

syntax natDiv m n = n div m
natDiv : (m : Nat) {nz : NonZero m} → Nat → Nat
natDiv zero {} n
natDiv (suc m) n = divAux 0 m n m

private
  modAux : Nat → Nat → Nat → Nat → Nat
  modAux k m  zero    j      = k
  modAux k m (suc n)  zero   = modAux 0 m n m
  modAux k m (suc n) (suc j) = modAux (suc k) m n j

  {-# BUILTIN NATMODSUCAUX modAux #-}

syntax natMod m n = n mod m
natMod : (m : Nat) {nz : NonZero m} → Nat → Nat
natMod zero {} n
natMod (suc m) n = modAux 0 m n m

--- Comparison ---

lessNat : Nat → Nat → Bool
lessNat  _        zero  = false
lessNat  zero   (suc _) = true
lessNat (suc n) (suc m) = lessNat n m

{-# BUILTIN NATLESS lessNat #-}

data LessNat : Nat → Nat → Set where
  diff : ∀ {n} k → LessNat n (n + suc k)

private
  -- Using unsafeCoerce here let's us compute the difference
  -- with only builtin functions (lessNat and _-_), which run
  -- fast on big naturals.
  compareNat : ∀ n m → Comparison LessNat n m
  compareNat n m with lessNat n m
  ... | true  = less $ unsafeCoerce $ diff {n} (m - suc n)
  ... | false with lessNat m n
  ...            | true  = greater $ unsafeCoerce $ diff {m} (n - suc m)
  ...            | false = equal unsafeEqual

OrdNat : Ord Nat
OrdNat = record { LessThan = LessNat ; compare = compareNat }

pred-monotone : ∀ n m → IsTrue (suc n < suc m) → IsTrue (n < m)
pred-monotone n m p with lessNat n m
pred-monotone n m _  | true  = _
pred-monotone n m p  | false with lessNat m n
pred-monotone n m () | false | true
pred-monotone n m () | false | false

min : Nat → Nat → Nat
min n m = if n < m then n else m

max : Nat → Nat → Nat
max n m = if n > m then n else m
