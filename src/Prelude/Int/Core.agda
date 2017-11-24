
module Prelude.Int.Core where

open import Prelude.Unit
open import Prelude.Empty
open import Prelude.Nat
open import Prelude.Number
open import Prelude.Semiring
open import Prelude.Ord

open import Agda.Builtin.Int public

neg : Nat → Int
neg zero    = pos zero
neg (suc n) = negsuc n
{-# INLINE neg #-}

-- Integers are numbers --

instance
  NumInt : Number Int
  Number.Constraint NumInt _ = ⊤
  Number.fromNat    NumInt n = pos n

  NegInt : Negative Int
  Negative.Constraint NegInt _ = ⊤
  Negative.fromNeg    NegInt n = neg n

-- Arithmetic --

_-NZ_ : Nat → Nat → Int
a -NZ b with compare a b
... | less (diff k _)    = negsuc k
... | equal _            = pos (a - b)  -- a - b instead of 0 makes it compile to Integer minus
... | greater (diff k _) = pos (suc k)
{-# INLINE _-NZ_ #-}

_+Z_ : Int → Int → Int
pos    a +Z pos    b = pos (a + b)
pos    a +Z negsuc b = a -NZ suc b
negsuc a +Z pos    b = b -NZ suc a
negsuc a +Z negsuc b = negsuc (suc a + b)
{-# INLINE _+Z_ #-}

{-# DISPLAY _+Z_ a b = a + b #-}

negateInt : Int → Int
negateInt (pos    n) = neg n
negateInt (negsuc n) = pos (suc n)
{-# INLINE negateInt #-}

{-# DISPLAY negateInt a = negate a #-}

_-Z_ : Int → Int → Int
a -Z b = a +Z negateInt b
{-# INLINE _-Z_ #-}

abs : Int → Nat
abs (pos n) = n
abs (negsuc n) = suc n

_*Z_ : Int → Int → Int
pos    a *Z pos    b = pos (a * b)
pos    a *Z negsuc b = neg (a * suc b)
negsuc a *Z pos    b = neg (suc a * b)
negsuc a *Z negsuc b = pos (suc a * suc b)
{-# INLINE _*Z_ #-}

{-# DISPLAY _*Z_ a b = a * b #-}

instance
  SemiringInt : Semiring Int
  Semiring.zro SemiringInt = 0
  Semiring.one SemiringInt = 1
  Semiring._+_ SemiringInt = _+Z_
  Semiring._*_ SemiringInt = _*Z_

  SubInt : Subtractive Int
  Subtractive._-_    SubInt = _-Z_
  Subtractive.negate SubInt = negateInt

NonZeroInt : Int → Set
NonZeroInt (pos zero) = ⊥
NonZeroInt _ = ⊤

infixl 7 quotInt-by remInt-by

syntax quotInt-by b a = a quot b
quotInt-by : (b : Int) {{_ : NonZeroInt b}} → Int → Int
quotInt-by (pos zero) {{}} _
quotInt-by (pos (suc n)) (pos m)    = pos (m div suc n)
quotInt-by (pos (suc n)) (negsuc m) = neg (suc m div suc n)
quotInt-by (negsuc n)    (pos m)    = neg (m div suc n)
quotInt-by (negsuc n)    (negsuc m) = pos (suc m div suc n)
{-# INLINE quotInt-by #-}

syntax remInt-by b a = a rem b
remInt-by : (b : Int) {{_ : NonZeroInt b}} → Int → Int
remInt-by (pos zero) {{}} _
remInt-by (pos (suc n)) (pos m)    = pos (    m mod suc n)
remInt-by (pos (suc n)) (negsuc m) = neg (suc m mod suc n)
remInt-by (negsuc n)    (pos m)    = pos (    m mod suc n)
remInt-by (negsuc n)    (negsuc m) = neg (suc m mod suc n)
{-# INLINE remInt-by #-}
