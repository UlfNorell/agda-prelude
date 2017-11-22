
module Prelude.Word where

import Agda.Builtin.Word as Word
open import Prelude.Nat
open import Prelude.Number
open import Prelude.Equality
open import Prelude.Equality.Unsafe
open import Prelude.Ord
open import Prelude.Unit
open import Prelude.Function
open import Prelude.Decidable

open Word using (Word64) public
open Word

private
  2⁶⁴ : Nat
  2⁶⁴ = 18446744073709551616

word64ToNat : Word64 → Nat
word64ToNat = primWord64ToNat

word64FromNat : Nat → Word64
word64FromNat = primWord64FromNat

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
