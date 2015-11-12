
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
{-# INLINE neg #-}

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

-- Eq --

pos-inj : ∀ {a b} → pos a ≡ pos b → a ≡ b
pos-inj refl = refl

negsuc-inj : ∀ {a b} → negsuc a ≡ negsuc b → a ≡ b
negsuc-inj refl = refl

neg-inj : ∀ {a b} → neg a ≡ neg b → a ≡ b
neg-inj {zero}  {zero}  eq = refl
neg-inj {zero}  {suc b} ()
neg-inj {suc a} {zero}  ()
neg-inj {suc a} {suc b} eq = suc $≡ negsuc-inj eq

instance
  EqInt : Eq Int
  Eq._==_ EqInt = eqInt
    where
      eqInt : ∀ x y → Dec (x ≡ y)
      eqInt (pos    n) (pos    m) = decEq₁ pos-inj (n == m)
      eqInt (pos    n) (negsuc m) = no λ ()
      eqInt (negsuc n) (pos    m) = no λ ()
      eqInt (negsuc n) (negsuc m) = decEq₁ negsuc-inj (n == m)

-- Ord --

data LessInt (a b : Int) : Set where
  diff : (k : Nat) (eq : b ≡ pos (suc k) + a) → LessInt a b

private
  nat-plus-zero : (a : Nat) → a + 0 ≡ a
  nat-plus-zero zero = refl
  nat-plus-zero (suc a) = suc $≡ nat-plus-zero a

  nat-plus-suc : (a b : Nat) → a + suc b ≡ suc (a + b)
  nat-plus-suc zero b = refl
  nat-plus-suc (suc a) b = suc $≡ nat-plus-suc a b

  nat-plus-commute : (a b : Nat) → a + b ≡ b + a
  nat-plus-commute a zero = nat-plus-zero a
  nat-plus-commute a (suc b) = nat-plus-suc a b ⟨≡⟩ suc $≡ nat-plus-commute a b

  nat-plus-assoc : (a b c : Nat) → a + (b + c) ≡ (a + b) + c
  nat-plus-assoc zero    b c = refl
  nat-plus-assoc (suc a) b c = suc $≡ nat-plus-assoc a b c

  nat-plus-neq-l : (a b : Nat) → a ≡ suc b + a → {A : Set} → A
  nat-plus-neq-l a zero ()
  nat-plus-neq-l zero (suc b) ()
  nat-plus-neq-l (suc a) (suc b) eq = nat-plus-neq-l a (suc b) (suc-inj eq ⟨≡⟩ suc $≡ nat-plus-suc b a)

  nat-plus-neq-r : (a b : Nat) → a ≡ a + suc b → {A : Set} → A
  nat-plus-neq-r a b eq = nat-plus-neq-l a b (eq ⟨≡⟩ nat-plus-commute a (suc b))

  nat-plus-inj₁ : (a a₁ b : Nat) → a + b ≡ a₁ + b → a ≡ a₁
  nat-plus-inj₁ zero zero b eq = refl
  nat-plus-inj₁ zero (suc a₁) b eq = nat-plus-neq-l b a₁ eq
  nat-plus-inj₁ (suc a) zero b eq = nat-plus-neq-l b a (sym eq)
  nat-plus-inj₁ (suc a) (suc a₁) b eq = suc $≡ nat-plus-inj₁ a a₁ b (suc-inj eq)

  nat-plus-inj₂ : (a b b₁ : Nat) → a + b ≡ a + b₁ → b ≡ b₁
  nat-plus-inj₂ a b b₁ eq = nat-plus-inj₁ b b₁ a (nat-plus-commute b a ⟨≡⟩ eq ⟨≡⟩ nat-plus-commute a b₁)

  negate-inj : (a b : Int) → negate a ≡ negate b → a ≡ b
  negate-inj (pos    a)    (pos    b)    eq = pos $≡ neg-inj eq
  negate-inj (pos  zero)   (negsuc b)    ()
  negate-inj (pos (suc a)) (negsuc b)    ()
  negate-inj (negsuc a)    (pos zero)    ()
  negate-inj (negsuc a)    (pos (suc _)) ()
  negate-inj (negsuc a)    (negsuc b)    eq = negsuc $≡ suc-inj (pos-inj eq)

  -- Spec for _-NZ_
  diffNat : Nat → Nat → Int
  diffNat a zero = pos a
  diffNat zero    (suc b) = negsuc b
  diffNat (suc a) (suc b) = diffNat a b

  lem-too-much-plus : ∀ a j k → suc a ≡ suc (j + suc (suc (k + a))) → {A : Set} → A
  lem-too-much-plus a j k eq =
    nat-plus-neq-l (suc a) (j + suc k)
      (eq ⟨≡⟩ suc $≡ (j +_ $≡ nat-plus-suc (suc k) a ʳ⟨≡⟩ nat-plus-assoc j _ _))

  lem-cancel-plus : ∀ {a b k k₁} → b ≡ suc (k + a) → suc b ≡ suc (k₁ + suc a) → k₁ ≡ k
  lem-cancel-plus {a} {k = k} eq eq₁ =
    nat-plus-inj₁ _ _ (suc a) (suc-inj eq₁ ʳ⟨≡⟩ eq ⟨≡⟩ʳ nat-plus-suc k a)

  diffnat-suc : ∀ a b → suc a -NZ suc b ≡ a -NZ b
  diffnat-suc a b with compare a b | compare (suc a) (suc b)
  diffnat-suc a b | less (diff k eq) | less (diff k₁ eq₁) = negsuc $≡ lem-cancel-plus eq eq₁
  diffnat-suc a .a | less (diff k eq) | equal refl = nat-plus-neq-l a k eq
  diffnat-suc a _ | less (diff k refl) | greater (diff j eq) = lem-too-much-plus a j k eq
  diffnat-suc a .a | equal refl | less (diff k eq₁) = nat-plus-neq-l (suc a) k eq₁
  diffnat-suc a b | equal eq | equal eq₁ = refl
  diffnat-suc a .a | equal refl | greater (diff k eq₁) = nat-plus-neq-l (suc a) k eq₁
  diffnat-suc _ b | greater (diff k refl) | less (diff j eq) = lem-too-much-plus b j k eq
  diffnat-suc _ b | greater (diff k refl) | equal eq = nat-plus-neq-l b k (sym (suc-inj eq))
  diffnat-suc a b | greater (diff k eq) | greater (diff k₁ eq₁) = pos $≡ (suc $≡ lem-cancel-plus eq eq₁)

  diffnat-spec : ∀ a b → a -NZ b ≡ diffNat a b
  diffnat-spec zero zero = refl
  diffnat-spec (suc a) zero = refl
  diffnat-spec zero (suc b) = refl
  diffnat-spec (suc a) (suc b) = diffnat-suc a b ⟨≡⟩ diffnat-spec a b

  predInt : Int → Int
  predInt (pos zero)    = negsuc zero
  predInt (pos (suc n)) = pos n
  predInt (negsuc n)    = negsuc (suc n)

  sucInt : Int → Int
  sucInt (pos n)          = pos (suc n)
  sucInt (negsuc zero)    = pos zero
  sucInt (negsuc (suc n)) = negsuc n

  sucInt-inj : ∀ a b → sucInt a ≡ sucInt b → a ≡ b
  sucInt-inj (pos n) (pos .n) refl = refl
  sucInt-inj (pos n) (negsuc zero) ()
  sucInt-inj (pos n) (negsuc (suc m)) ()
  sucInt-inj (negsuc zero) (pos m) ()
  sucInt-inj (negsuc (suc n)) (pos m) ()
  sucInt-inj (negsuc zero) (negsuc zero) eq = refl
  sucInt-inj (negsuc zero) (negsuc (suc m)) ()
  sucInt-inj (negsuc (suc n)) (negsuc zero) ()
  sucInt-inj (negsuc (suc n)) (negsuc (suc .n)) refl = refl

  lem-suc-plus1 : ∀ a → sucInt a ≡ 1 + a
  lem-suc-plus1 (pos n) = refl
  lem-suc-plus1 (negsuc zero) = refl
  lem-suc-plus1 (negsuc (suc n)) = refl

  lem-suc-diff : ∀ a b → sucInt (diffNat a b) ≡ diffNat (suc a) b
  lem-suc-diff a zero = refl
  lem-suc-diff zero (suc zero) = refl
  lem-suc-diff zero (suc (suc b)) = refl
  lem-suc-diff (suc a) (suc b) = lem-suc-diff a b

  lem-suc-minus : ∀ a b → sucInt (a -NZ b) ≡ suc a -NZ b
  lem-suc-minus a b =
    sucInt $≡ diffnat-spec a b ⟨≡⟩
    lem-suc-diff a b ⟨≡⟩ʳ
    diffnat-spec (suc a) b

  lem-plus1-minus : ∀ a b → 1 + (a -NZ b) ≡ suc a -NZ b
  lem-plus1-minus a b = lem-suc-plus1 (a -NZ b) ʳ⟨≡⟩ lem-suc-minus a b

  lem-suc-plus-l : ∀ a b → sucInt a + b ≡ sucInt (a + b)
  lem-suc-plus-l (pos n) (pos m) = refl
  lem-suc-plus-l (pos n) (negsuc m) = sym (lem-suc-minus n (suc m))
  lem-suc-plus-l (negsuc zero) (pos m) = diffnat-spec (suc m) 1 ʳ⟨≡⟩ʳ lem-suc-minus m 1
  lem-suc-plus-l (negsuc (suc n)) (pos m) =
    diffnat-spec m (suc n) ⟨≡⟩ lem-suc-diff m (suc (suc n)) ʳ⟨≡⟩ʳ sucInt $≡ diffnat-spec m (suc (suc n))
  lem-suc-plus-l (negsuc zero) (negsuc m) = refl
  lem-suc-plus-l (negsuc (suc n)) (negsuc m) = refl

  lem-eq-diff : (n m : Nat) → diffNat n m ≡ 0 → n ≡ m
  lem-eq-diff .zero zero refl = refl
  lem-eq-diff zero (suc m) ()
  lem-eq-diff (suc n) (suc m) eq = suc $≡ lem-eq-diff n m eq

  lem-eq-minus : (n m : Nat) → n -NZ m ≡ 0 → n ≡ m
  lem-eq-minus n m eq = lem-eq-diff n m (diffnat-spec n m ʳ⟨≡⟩ eq)

  lem-equal : (a b : Int) → a - b ≡ 0 → a ≡ b
  lem-equal (pos n) (pos zero) eq = pos $≡ (nat-plus-zero n ʳ⟨≡⟩ pos-inj eq)
  lem-equal (pos n) (pos (suc m)) eq = pos $≡ lem-eq-minus n (suc m) eq
  lem-equal (pos    n) (negsuc m) eq = case nat-plus-suc n m ʳ⟨≡⟩ pos-inj eq of λ ()
  lem-equal (negsuc n) (pos zero) ()
  lem-equal (negsuc n) (pos (suc m)) ()
  lem-equal (negsuc n) (negsuc m) eq = negsuc $≡ sym (suc-inj (lem-eq-minus (suc m) (suc n) eq))

  lem-diff-neg : (a b : Nat) → diffNat a (a + suc b) ≡ negsuc b
  lem-diff-neg zero b = refl
  lem-diff-neg (suc a) b = lem-diff-neg a b

  lem-minus-neg : (a b : Nat) → a -NZ (a + suc b) ≡ negsuc b
  lem-minus-neg a b = diffnat-spec a (a + suc b) ⟨≡⟩ lem-diff-neg a b

  diffnat-cancel : ∀ a → diffNat a a ≡ 0
  diffnat-cancel zero = refl
  diffnat-cancel (suc a) = diffnat-cancel a

  lem-diff-pos : (a b : Nat) → diffNat (a + b) b ≡ pos a
  lem-diff-pos zero b = diffnat-cancel b
  lem-diff-pos (suc a) zero = pos $≡ nat-plus-zero (suc a)
  lem-diff-pos (suc a) (suc b) = flip diffNat b $≡ nat-plus-suc a b ⟨≡⟩ lem-diff-pos (suc a) b

  lem-minus-pos : (a b : Nat) → (a + b) -NZ b ≡ pos a
  lem-minus-pos a b = diffnat-spec (a + b) b ⟨≡⟩ lem-diff-pos a b

  lem-greater-diff : ∀ n m k → diffNat n m ≡ pos k → n ≡ k + m
  lem-greater-diff _ zero k refl = sym (nat-plus-zero k)
  lem-greater-diff zero (suc m) k ()
  lem-greater-diff (suc n) (suc m) k eq = suc $≡ lem-greater-diff n m k eq ⟨≡⟩ʳ nat-plus-suc k m

  lem-greater-minus : ∀ n m k → n -NZ m ≡ pos k → n ≡ k + m
  lem-greater-minus n m k eq = lem-greater-diff n m k (diffnat-spec n m ʳ⟨≡⟩ eq)

  lem-greater : (a b : Int) (k : Nat) → a - b ≡ pos (suc k) → a ≡ pos (suc k) + b
  lem-greater (pos n)    (pos zero)    k eq = pos $≡ (nat-plus-zero n ʳ⟨≡⟩ pos-inj eq ⟨≡⟩ʳ suc $≡ nat-plus-zero k)
  lem-greater (pos n)    (pos (suc m)) k eq = pos $≡ lem-greater-minus n (suc m) (suc k) eq
  lem-greater (pos n)    (negsuc m)    k eq = lem-minus-pos n (suc m) ʳ⟨≡⟩ _-NZ suc m $≡ pos-inj eq
  lem-greater (negsuc n) (pos zero)    k ()
  lem-greater (negsuc n) (pos (suc m)) k ()
  lem-greater (negsuc n) (negsuc m)    k eq = lem-minus-neg (suc k) n ʳ⟨≡⟩ʳ
                                              suc k -NZ_ $≡ lem-greater-minus (suc m) (suc n) (suc k) eq

  lem-less-diff : ∀ n m k → diffNat n m ≡ negsuc k → m ≡ suc k + n
  lem-less-diff n zero k ()
  lem-less-diff zero (suc m) .m refl = nat-plus-commute 0 (suc m)
  lem-less-diff (suc n) (suc m) k eq = suc $≡ lem-less-diff n m k eq ⟨≡⟩ʳ nat-plus-suc (suc k) n

  lem-less-minus : ∀ n m k → n -NZ m ≡ negsuc k → m ≡ suc k + n
  lem-less-minus n m k eq = lem-less-diff n m k (diffnat-spec n m ʳ⟨≡⟩ eq)

  lem-less : (a b : Int) (k : Nat) → a - b ≡ negsuc k → b ≡ pos (suc k) + a
  lem-less (pos n)    (pos zero)    k ()
  lem-less (pos n)    (pos (suc m)) k eq   = pos $≡ lem-less-minus n (suc m) k eq
  lem-less (pos n)    (negsuc m)    k ()
  lem-less (negsuc n) (pos zero)    _ refl = diffnat-cancel n ʳ⟨≡⟩ʳ diffnat-spec (suc n) (suc n)
  lem-less (negsuc n) (pos (suc m)) _ refl = lem-minus-pos (suc m) (suc n) ʳ⟨≡⟩
                                             _-NZ suc n $≡ (suc $≡ nat-plus-commute m (suc n))
  lem-less (negsuc n) (negsuc m)    k eq   = lem-minus-neg (suc k) m ʳ⟨≡⟩ʳ
                                             suc k -NZ_ $≡ lem-less-minus (suc m) (suc n) k eq

compareInt : (a b : Int) → Comparison LessInt a b
compareInt a b with inspect (a - b)
compareInt a b | pos zero    with≡ eq = equal (eraseEquality (lem-equal a b eq))
compareInt a b | pos (suc k) with≡ eq = greater (diff k (eraseEquality (lem-greater a b k eq)))
compareInt a b | negsuc k    with≡ eq = less (diff k (eraseEquality (lem-less a b k eq)))
{-# INLINE compareInt #-}

private
  from-eq : ∀ x y → x ≡ y → LessInt x (1 + y)
  from-eq x .x refl = diff 0 refl

  from-lt : ∀ x y → LessInt x y → LessInt x (1 + y)
  from-lt (pos n)    _ (diff k refl) = diff (suc k) refl
  from-lt (negsuc n) _ (diff k refl) = diff (suc k) (lem-plus1-minus (suc k) (suc n))

  from-leq : ∀ x y → LessInt x (1 + y) → LessEq LessInt x y
  from-leq x y (diff zero eq) = equal (sucInt-inj x y (lem-suc-plus1 x ⟨≡⟩ eq ʳ⟨≡⟩ʳ lem-suc-plus1 y))
  from-leq x y (diff (suc k) eq) =
    less (diff k (sucInt-inj y (_+_ (pos (suc k)) x)
      (lem-suc-plus1 y ⟨≡⟩ eq ⟨≡⟩ lem-suc-plus-l (pos (suc k)) x)
    ))

instance
  OrdInt : Ord Int
  Ord._<_         OrdInt = _
  Ord._≤_         OrdInt a b = LessInt a (1 + b)
  Ord.compare     OrdInt = compareInt
  Ord.eq-to-leq   OrdInt = from-eq _ _
  Ord.lt-to-leq   OrdInt = from-lt _ _
  Ord.leq-to-lteq OrdInt = from-leq _ _

open import Prelude.Function
