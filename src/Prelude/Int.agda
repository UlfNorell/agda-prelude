
module Prelude.Int where

open import Prelude.Unit
open import Prelude.Empty
open import Prelude.Nat
open import Prelude.Number
open import Prelude.String
open import Prelude.Semiring
open import Prelude.Equality
open import Prelude.Equality.Inspect
open import Prelude.Equality.Unsafe using (eraseEquality)
open import Prelude.Ord
open import Prelude.Decidable
open import Prelude.Function
open import Prelude.Nat.Properties
open import Prelude.Int.Properties

open import Prelude.Int.Core public

open import Agda.Builtin.Int public

private
  subInt-cancel-r : (a b c : Int) → a - b ≡ c → c + b ≡ a
  subInt-cancel-r a b c refl =
    addInt-assoc a (negate b) b ʳ⟨≡⟩
    a +_ $≡ (addInt-commute (negate b) b ⟨≡⟩ subInt-equal b _ refl) ⟨≡⟩
    addInt-zero-r a

  lem-equal : (a b : Int) → a - b ≡ 0 → a ≡ b
  lem-equal a b eq = subInt-cancel-r a b 0 eq ʳ⟨≡⟩ addInt-zero-l b

  lem-less : (a b c : Int) → a - b ≡ c → negate c + a ≡ b
  lem-less a b c eq = subInt-cancel-r b a (negate c) (negate-subInt a b ʳ⟨≡⟩ negate $≡ eq)

-- Eq --

instance
  EqInt : Eq Int
  Eq._==_ EqInt = eqInt
    where
      eqInt : (a b : Int) → Dec (a ≡ b)
      eqInt a b with inspect (a - b)
      eqInt a b | pos zero    with≡ eq = yes (lem-equal a b eq)
      eqInt a b | pos (suc n) with≡ eq = no λ a=b → case subInt-equal _ _ a=b ʳ⟨≡⟩ eq of λ ()
      eqInt a b | negsuc n    with≡ eq = no λ a=b → case subInt-equal _ _ a=b ʳ⟨≡⟩ eq of λ ()

-- Ord --

data LessInt (a b : Int) : Set where
  diff : (k : Nat) (eq : b ≡ pos (suc k) + a) → LessInt a b

compareInt : (a b : Int) → Comparison LessInt a b
compareInt a b with inspect (a - b)
compareInt a b | pos zero        with≡ eq = equal           (eraseEquality (lem-equal a b eq))
compareInt a b | c@(pos (suc k)) with≡ eq = greater (diff k (eraseEquality (sym (subInt-cancel-r a b c eq))))
compareInt a b | c@(negsuc k)    with≡ eq = less    (diff k (eraseEquality (sym (lem-less a b c eq))))
{-# INLINE compareInt #-}

private
  from-eq : ∀ x y → x ≡ y → LessInt x (1 + y)
  from-eq x y eq = diff 0 (eraseEquality (1 +_ $≡ sym eq))

  from-lt : ∀ x y → LessInt x y → LessInt x (1 + y)
  from-lt (pos n)    _ (diff k eq) = diff (suc k) (eraseEquality (1 +_ $≡ eq))
  from-lt (negsuc n) _ (diff k eq) = diff (suc k) (eraseEquality (
    1 +_ $≡ eq ⟨≡⟩ addInt-pos 1 (suc k -NZ suc n) ⟨≡⟩ʳ
    -NZ-suc-l (suc k) (suc n)))

  from-leq : ∀ x y → LessInt x (1 + y) → LessEq LessInt x y
  from-leq x y (diff zero eq) = equal (eraseEquality (addInt-inj₂ 1 x y (sym eq)))
  from-leq x y (diff (suc k) eq) =
    less (diff k (eraseEquality (sucInt-inj y (_+_ (pos (suc k)) x)
                                  (addInt-pos 1 y ʳ⟨≡⟩ eq ⟨≡⟩ addInt-sucInt-l (pos (suc k)) x))))

instance
  OrdInt : Ord Int
  Ord._<_         OrdInt = _
  Ord._≤_         OrdInt a b = LessInt a (1 + b)
  Ord.compare     OrdInt = compareInt
  Ord.eq-to-leq   OrdInt = from-eq _ _
  Ord.lt-to-leq   OrdInt = from-lt _ _
  Ord.leq-to-lteq OrdInt = from-leq _ _

-- Ord/Laws --

private
  lessInt-antirefl : (a : Int) → a < a → ⊥
  lessInt-antirefl a (diff k eq) = case addInt-inj₁ 0 (pos (suc k)) a (addInt-zero-l a ⟨≡⟩ eq) of λ ()

  lessInt-antisym : (a b : Int) → a < b → b < a → ⊥
  lessInt-antisym a b (diff k refl) (diff j eq) =
    case addInt-inj₁ 0 (pos (suc j) + pos (suc k)) a
           (addInt-zero-l a ⟨≡⟩ eq ⟨≡⟩ addInt-assoc (pos (suc j)) (pos (suc k)) a)
    of λ ()

  lessInt-trans : {a b c : Int} → a < b → b < c → a < c
  lessInt-trans {a} (diff k eq) (diff j eq₁) = diff (j + suc k) (eraseEquality $
    case eq of λ where
      refl → case eq₁ of λ where
        refl → addInt-assoc (pos (suc j)) (pos (suc k)) a)

instance
  OrdIntLaws : Ord/Laws Int
  Ord/Laws.super OrdIntLaws = it
  less-antirefl {{OrdIntLaws}} = lessInt-antirefl _
  less-trans    {{OrdIntLaws}} = lessInt-trans
