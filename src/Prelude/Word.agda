
module Prelude.Word where

import Agda.Builtin.Word as Word
open import Prelude.Nat
open import Prelude.Number
open import Prelude.Semiring
open import Prelude.Equality
open import Prelude.Equality.Unsafe
open import Prelude.Ord
open import Prelude.Unit
open import Prelude.Function
open import Prelude.Decidable

open Word public using (Word64) renaming (primWord64ToNat to word64ToNat;
                                          primWord64FromNat to word64FromNat)
open Word

private
  2⁶⁴ : Nat
  2⁶⁴ = 18446744073709551616
  {-# INLINE 2⁶⁴ #-}

inv-word64ToNat : ∀ {a} → word64FromNat (word64ToNat a) ≡ a
inv-word64ToNat = unsafeEqual

emb-word64FromNat : ∀ n → word64ToNat (word64FromNat n) ≡ n mod 2⁶⁴
emb-word64FromNat n = unsafeEqual

inj-word64ToNat : ∀ {a b} → word64ToNat a ≡ word64ToNat b → a ≡ b
inj-word64ToNat {a} {b} eq =
  a ≡⟨ inv-word64ToNat ⟩ʳ
  word64FromNat (word64ToNat a)
    ≡⟨ word64FromNat $≡ eq ⟩
  word64FromNat (word64ToNat b)
    ≡⟨ inv-word64ToNat ⟩
  b ∎

instance
  NumWord64 : Number Word64
  Number.Constraint NumWord64 _ = ⊤
  fromNat {{NumWord64}} n = word64FromNat n

  EqWord64 : Eq Word64
  _==_ {{EqWord64}} a b =
    case word64ToNat a == word64ToNat b of λ where
      (yes _) → yes unsafeEqual
      (no  _) → no  unsafeNotEqual

  OrdWord64 : Ord Word64
  OrdWord64 = OrdBy inj-word64ToNat

  OrdLawsWord64 : Ord/Laws Word64
  OrdLawsWord64 = OrdLawsBy inj-word64ToNat

-- Arithmetic --

private
  natOp : (Nat → Nat → Nat) → Word64 → Word64 → Word64
  natOp f a b = fromNat (f (word64ToNat a) (word64ToNat b))
  {-# INLINE natOp #-}

add64 : Word64 → Word64 → Word64
add64 = natOp _+_

sub64 : Word64 → Word64 → Word64
sub64 = natOp λ a b → a + 2⁶⁴ - b

mul64 : Word64 → Word64 → Word64
mul64 = natOp _*_

{-# INLINE add64 #-}
{-# INLINE sub64 #-}
{-# INLINE mul64 #-}

NonZero64 : Word64 → Set
NonZero64 a = NonZero (word64ToNat a)

infixl 7 divWord64 modWord64

syntax divWord64 b a = a div64 b
divWord64 : (b : Word64) {{nz : NonZero64 b}} → Word64 → Word64
divWord64 b a = fromNat (word64ToNat a div word64ToNat b)

syntax modWord64 b a = a mod64 b
modWord64 : (b : Word64) {{nz : NonZero64 b}} → Word64 → Word64
modWord64 b a = fromNat (word64ToNat a mod word64ToNat b)

{-# INLINE divWord64 #-}
{-# INLINE modWord64 #-}

instance
  SemiringWord64 : Semiring Word64
  Semiring.zro SemiringWord64 = 0
  Semiring.one SemiringWord64 = 1
  Semiring._+_ SemiringWord64 = add64
  Semiring._*_ SemiringWord64 = mul64

  NegWord64 : Negative Word64
  Negative.Constraint NegWord64 _ = ⊤
  fromNeg {{NegWord64}} n = sub64 0 (fromNat n)

  SubWord64 : Subtractive Word64
  _-_    {{SubWord64}} = sub64
  negate {{SubWord64}} = sub64 0
