
module Prelude.Int where

open import Prelude.Unit
open import Prelude.Nat
open import Prelude.Number
open import Prelude.String
open import Prelude.Show
open import Prelude.Semiring
open import Prelude.Equality
open import Prelude.Ord
open import Prelude.Decidable

data Int : Set where
  pos    : (n : Nat) → Int
  negsuc : (n : Nat) → Int

{-# BUILTIN INTEGER       Int    #-}
{-# BUILTIN INTEGERPOS    pos    #-}
{-# BUILTIN INTEGERNEGSUC negsuc #-}

-- Integers are numbers --

neg : Nat → Int
neg zero    = pos zero
neg (suc n) = negsuc n

instance
  NumInt : Number Int
  Number.Constraint NumInt _ = ⊤
  Number.fromNat    NumInt n = pos n

  NegInt : Negative Int
  Negative.Constraint NegInt _ = ⊤
  Negative.fromNeg    NegInt n = neg n

-- Primitive show saves us a bit of code --

private
 primitive
  primShowInteger : Int → String

instance
  ShowInt : Show Int
  ShowInt = simpleShowInstance primShowInteger

-- Arithmetic --

_-NZ_ : Nat → Nat → Int
a -NZ b with compare a b
... | less (diff k _)    = negsuc k
... | equal _            = pos zero
... | greater (diff k _) = pos (suc k)

_+Z_ : Int → Int → Int
pos    a +Z pos    b = pos (a + b)
pos    a +Z negsuc b = a -NZ suc b
negsuc a +Z pos    b = b -NZ suc a
negsuc a +Z negsuc b = negsuc (suc a + b)

{-# DISPLAY _+Z_ a b = a + b #-}

negateInt : Int → Int
negateInt (pos    n) = neg n
negateInt (negsuc n) = pos (suc n)

{-# DISPLAY negateInt a = negate a #-}

_-Z_ : Int → Int → Int
a -Z b = a +Z negateInt b

_*Z_ : Int → Int → Int
pos    a *Z pos    b = pos (a * b)
pos    a *Z negsuc b = neg (a * suc b)
negsuc a *Z pos    b = neg (suc a * b)
negsuc a *Z negsuc b = neg (suc a * suc b)

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

-- Eq --

pos-inj : ∀ {a b} → pos a ≡ pos b → a ≡ b
pos-inj refl = refl

negsuc-inj : ∀ {a b} → negsuc a ≡ negsuc b → a ≡ b
negsuc-inj refl = refl

instance
  EqInt : Eq Int
  Eq._==_ EqInt = eqInt
    where
      eqInt : ∀ x y → Dec (x ≡ y)
      eqInt (pos    n) (pos    m) = decEq₁ pos-inj (n == m)
      eqInt (pos    n) (negsuc m) = no λ ()
      eqInt (negsuc n) (pos    m) = no λ ()
      eqInt (negsuc n) (negsuc m) = decEq₁ negsuc-inj (n == m)

data LessInt : Int → Int → Set where
  neg<pos : ∀ {n m} → LessInt (negsuc n) (pos m)
  pos<pos : ∀ {n m} → n < m → LessInt (pos n) (pos m)
  neg<neg : ∀ {n m} → n < m → LessInt (negsuc m) (negsuc n)

compareInt : (a b : Int) → Comparison LessInt a b
compareInt (pos    n) (pos    m) = mapComparison pos<pos (compare n m)
compareInt (pos    n) (negsuc m) = greater neg<pos
compareInt (negsuc n) (pos    m) = less    neg<pos
compareInt (negsuc n) (negsuc m) = mapComparison neg<neg (flipComparison (compare n m))

instance
  OrdInt : Ord Int
  OrdInt = defaultOrd compareInt
