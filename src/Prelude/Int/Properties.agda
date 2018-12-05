
module Prelude.Int.Properties where

open import Prelude.Unit
open import Prelude.Nat
open import Prelude.Nat.Properties
open import Prelude.Number
open import Prelude.Equality
open import Prelude.Int.Core
open import Prelude.Smashed
open import Prelude.Ord
open import Prelude.Semiring
open import Prelude.Function

--- Specification functions ---
---   sucInt   a   =  1 + a
---   predInt  a   = -1 + a
---   sucsInt  n a = pos n + a
---   predsInt n a = neg n + a
---   diffNat  a b = a -NZ b

sucInt : Int → Int
sucInt (pos n)          = pos (suc n)
sucInt (negsuc zero)    = pos zero
sucInt (negsuc (suc n)) = negsuc n

predInt : Int → Int
predInt (pos zero)    = negsuc zero
predInt (pos (suc n)) = pos n
predInt (negsuc n)    = negsuc (suc n)

sucsInt : Nat → Int → Int
sucsInt zero    b = b
sucsInt (suc a) b = sucInt (sucsInt a b)

predsInt : Nat → Int → Int
predsInt zero    b = b
predsInt (suc a) b = predInt (predsInt a b)

diffNat : Nat → Nat → Int
diffNat a       zero    = pos a
diffNat zero    (suc b) = negsuc b
diffNat (suc a) (suc b) = diffNat a b

--- Injectivity proofs ---

pos-inj : ∀ {a b} → pos a ≡ pos b → a ≡ b
pos-inj refl = refl

negsuc-inj : ∀ {a b} → negsuc a ≡ negsuc b → a ≡ b
negsuc-inj refl = refl

neg-inj : ∀ {a b} → neg a ≡ neg b → a ≡ b
neg-inj {zero}  {zero}  eq = refl
neg-inj {zero}  {suc b} ()
neg-inj {suc a} {zero}  ()
neg-inj {suc a} {suc b} eq = suc $≡ negsuc-inj eq

negate-inj : {a b : Int} → negate a ≡ negate b → a ≡ b
negate-inj {pos    a}    {pos    b}    eq = pos $≡ neg-inj eq
negate-inj {pos  zero}   {negsuc b}    ()
negate-inj {pos (suc a)} {negsuc b}    ()
negate-inj {negsuc a}    {pos zero}    ()
negate-inj {negsuc a}    {pos (suc _)} ()
negate-inj {negsuc a}    {negsuc b}    eq = negsuc $≡ suc-inj (pos-inj eq)

sucInt-inj : ∀ a b → sucInt a ≡ sucInt b → a ≡ b
sucInt-inj (pos a)          (pos a)          refl = refl
sucInt-inj (pos a)          (negsuc zero)    ()
sucInt-inj (pos a)          (negsuc (suc b)) ()
sucInt-inj (negsuc zero)    (pos b) ()
sucInt-inj (negsuc (suc a)) (pos b) ()
sucInt-inj (negsuc zero)    (negsuc zero)    eq = refl
sucInt-inj (negsuc zero)    (negsuc (suc b)) ()
sucInt-inj (negsuc (suc a)) (negsuc zero)    ()
sucInt-inj (negsuc (suc a)) (negsuc (suc a)) refl = refl

predInt-inj : ∀ a b → predInt a ≡ predInt b → a ≡ b
predInt-inj (pos zero)    (pos zero)    eq = refl
predInt-inj (pos zero)    (pos (suc b)) ()
predInt-inj (pos (suc a)) (pos zero)    ()
predInt-inj (pos (suc a)) (pos (suc a)) refl = refl
predInt-inj (pos zero)    (negsuc b)    ()
predInt-inj (pos (suc a)) (negsuc b)    ()
predInt-inj (negsuc a)    (pos zero)    ()
predInt-inj (negsuc a)    (pos (suc b)) ()
predInt-inj (negsuc a)    (negsuc a)    refl = refl

--- sucInt and predInt are inverses --

sucInt-predInt : ∀ a → sucInt (predInt a) ≡ a
sucInt-predInt (pos zero)    = refl
sucInt-predInt (pos (suc n)) = refl
sucInt-predInt (negsuc n)    = refl

predInt-sucInt : ∀ a → predInt (sucInt a) ≡ a
predInt-sucInt (pos n)          = refl
predInt-sucInt (negsuc zero)    = refl
predInt-sucInt (negsuc (suc n)) = refl

--- Commutativity of _+_ is easy

addInt-commute : (a b : Int) → a + b ≡ b + a
addInt-commute (pos    a) (pos    b) = pos $≡ add-commute a b
addInt-commute (pos    a) (negsuc b) = refl
addInt-commute (negsuc a) (pos    b) = refl
addInt-commute (negsuc a) (negsuc b) = negsuc ∘ suc $≡ add-commute a b

--- Proving _-NZ_ == diffNat

-NZ-suc : ∀ a b → suc a -NZ suc b ≡ a -NZ b
-NZ-suc a b rewrite smashed {x = compare (suc a) (suc b)} {suc-comparison (compare a b)}
            with    compare a b
... | less    (diff! k) = refl
... | equal   eq        = refl
... | greater (diff! k) = refl

-NZ-spec : ∀ a b → a -NZ b ≡ diffNat a b
-NZ-spec zero    zero    = refl
-NZ-spec (suc a) zero    = refl
-NZ-spec zero    (suc b) = refl
-NZ-spec (suc a) (suc b) = -NZ-suc a b ⟨≡⟩ -NZ-spec a b

--- diffNat distributes over suc in both arguments...

diffNat-suc-l : ∀ a b → diffNat (suc a) b ≡ sucInt (diffNat a b)
diffNat-suc-l a       0             = refl
diffNat-suc-l 0       1             = refl
diffNat-suc-l 0       (suc (suc b)) = refl
diffNat-suc-l (suc a) (suc b)       = diffNat-suc-l a b

diffNat-suc-r : ∀ a b → diffNat a (suc b) ≡ predInt (diffNat a b)
diffNat-suc-r zero    zero    = refl
diffNat-suc-r zero    (suc b) = refl
diffNat-suc-r (suc a) zero    = refl
diffNat-suc-r (suc a) (suc b) = diffNat-suc-r a b

--- ...and thus so does _-NZ_

-NZ-suc-l : ∀ a b → suc a -NZ b ≡ sucInt (a -NZ b)
-NZ-suc-l a b = -NZ-spec (suc a) b ⟨≡⟩ diffNat-suc-l a b ⟨≡⟩ʳ sucInt $≡ -NZ-spec a b

-NZ-suc-r : ∀ a b → a -NZ suc b ≡ predInt (a -NZ b)
-NZ-suc-r a b = -NZ-spec a (suc b) ⟨≡⟩ diffNat-suc-r a b ⟨≡⟩ʳ predInt $≡ -NZ-spec a b

--- We need some lemmas about how sucInt and predInt relates to _+_.
--- These are special cases of the computation rules below, so we make them private.

private
  sucInt-spec : ∀ a → 1 + a ≡ sucInt a
  sucInt-spec (pos n)          = refl
  sucInt-spec (negsuc zero)    = refl
  sucInt-spec (negsuc (suc n)) = refl

  predInt-spec : ∀ a → -1 + a ≡ predInt a
  predInt-spec (pos zero)    = refl
  predInt-spec (pos (suc n)) = -NZ-spec (suc n) 1
  predInt-spec (negsuc n)    = refl

  addInt-suc : ∀ a b → pos (suc a) + b ≡ sucInt (pos a + b)
  addInt-suc a (pos    b) = refl
  addInt-suc a (negsuc b) = -NZ-suc-l a (suc b)

  addInt-negsuc : ∀ a b → negsuc (suc a) + b ≡ predInt (negsuc a + b)
  addInt-negsuc a (pos b)    = -NZ-suc-r b (suc a)
  addInt-negsuc a (negsuc b) = refl

--- Now we can prove some "computation" rules for _+_

addInt-zero-l : (a : Int) → 0 + a ≡ a
addInt-zero-l (pos a)    = refl
addInt-zero-l (negsuc a) = -NZ-spec 0 (suc a)

addInt-zero-r : (a : Int) → a + 0 ≡ a
addInt-zero-r (pos a)    = pos $≡ add-zero-r a
addInt-zero-r (negsuc a) = -NZ-spec 0 (suc a)

addInt-sucInt-l : ∀ a b → sucInt a + b ≡ sucInt (a + b)
addInt-sucInt-l (pos a)          b = addInt-suc a b
addInt-sucInt-l (negsuc zero)    b = addInt-zero-l b ⟨≡⟩ʳ sucInt $≡ predInt-spec b ⟨≡⟩ sucInt-predInt b
addInt-sucInt-l (negsuc (suc a)) b = sucInt-predInt (negsuc a + b) ʳ⟨≡⟩ʳ sucInt $≡ addInt-negsuc a b

addInt-predInt-l : ∀ a b → predInt a + b ≡ predInt (a + b)
addInt-predInt-l (pos zero)    b = predInt-spec b ⟨≡⟩ʳ predInt $≡ addInt-zero-l b
addInt-predInt-l (pos (suc a)) b = predInt-sucInt (pos a + b) ʳ⟨≡⟩ʳ predInt $≡ addInt-suc a b
addInt-predInt-l (negsuc a)    b = addInt-negsuc a b

--- Adding a non-negative number is equivalent to sucsInt and adding a negative number
--- to predsInt.

addInt-pos : ∀ a b → pos a + b ≡ sucsInt a b
addInt-pos zero    b = addInt-zero-l b
addInt-pos (suc a) b = addInt-suc a b ⟨≡⟩ sucInt $≡ addInt-pos a b

addInt-neg : ∀ a b → neg a + b ≡ predsInt a b
addInt-neg zero          b = addInt-zero-l b
addInt-neg (suc zero)    b = addInt-predInt-l 0 b ⟨≡⟩ predInt $≡ addInt-zero-l b -- predInt-spec b
addInt-neg (suc (suc a)) b = addInt-predInt-l (negsuc a) b ⟨≡⟩ predInt $≡ addInt-neg (suc a) b

--- sucsInt and predsInt have the appropriate associativity properties

private
  sucsInt-assoc : ∀ a b c → sucsInt a (b + c) ≡ sucsInt a b + c
  sucsInt-assoc zero    b c = refl
  sucsInt-assoc (suc a) b c = sucInt $≡ sucsInt-assoc a b c ⟨≡⟩ʳ
                              addInt-sucInt-l (sucsInt a b) c

  predsInt-assoc : ∀ a b c → predsInt a (b + c) ≡ predsInt a b + c
  predsInt-assoc zero    b c = refl
  predsInt-assoc (suc a) b c = predInt $≡ predsInt-assoc a b c ⟨≡⟩ʳ
                               addInt-predInt-l (predsInt a b) c

--- Finally we can prove associativity of _+_

addInt-assoc : (a b c : Int) → a + (b + c) ≡ (a + b) + c
addInt-assoc (pos    a) b c = addInt-pos a (b + c)       ⟨≡⟩ sucsInt-assoc a b c        ⟨≡⟩ʳ _+ c $≡ addInt-pos a b
addInt-assoc (negsuc a) b c = addInt-neg (suc a) (b + c) ⟨≡⟩ predsInt-assoc (suc a) b c ⟨≡⟩ʳ _+ c $≡ addInt-neg (suc a) b

--- Injectivity of _+_

private
  sucsInt-inj : ∀ a b c → sucsInt a b ≡ sucsInt a c → b ≡ c
  sucsInt-inj zero    b c eq = eq
  sucsInt-inj (suc a) b c eq = sucsInt-inj a b c (sucInt-inj _ _ eq)

  predsInt-inj : ∀ a b c → predsInt a b ≡ predsInt a c → b ≡ c
  predsInt-inj zero    b c eq = eq
  predsInt-inj (suc a) b c eq = predsInt-inj a b c (predInt-inj _ _ eq)

addInt-inj₂ : (a b c : Int) → a + b ≡ a + c → b ≡ c
addInt-inj₂ (pos a)    b c eq = sucsInt-inj  a b c                  (addInt-pos a b       ʳ⟨≡⟩ eq ⟨≡⟩ addInt-pos a c)
addInt-inj₂ (negsuc a) b c eq = predsInt-inj a b c (predInt-inj _ _ (addInt-neg (suc a) b ʳ⟨≡⟩ eq ⟨≡⟩ addInt-neg (suc a) c))

addInt-inj₁ : (a b c : Int) → a + c ≡ b + c → a ≡ b
addInt-inj₁ a b c eq = addInt-inj₂ c a b (addInt-commute c a ⟨≡⟩ eq ⟨≡⟩ addInt-commute b c)

--- Properties of negate ---

negate-idempotent : (a : Int) → negate (negate a) ≡ a
negate-idempotent (pos zero)    = refl
negate-idempotent (pos (suc n)) = refl
negate-idempotent (negsuc n)    = refl

private
  neg-add : ∀ a b → neg (a + b) ≡ neg a + neg b
  neg-add zero    b       = sym (addInt-zero-l (neg b))
  neg-add (suc a) zero    = negsuc $≡ add-zero-r a ⟨≡⟩ʳ -NZ-spec 0 (suc a)
  neg-add (suc a) (suc b) = negsuc $≡ add-suc-r a b

  negate-diffNat : ∀ a b → negate (diffNat a b) ≡ diffNat b a
  negate-diffNat zero    zero    = refl
  negate-diffNat zero    (suc b) = refl
  negate-diffNat (suc a) zero    = refl
  negate-diffNat (suc a) (suc b) = negate-diffNat a b

negate-NZ : ∀ a b → negate (a -NZ b) ≡ b -NZ a
negate-NZ a b = negate $≡ -NZ-spec a b ⟨≡⟩ negate-diffNat a b ⟨≡⟩ʳ -NZ-spec b a

negate-addInt : (a b : Int) → negate (a + b) ≡ negate a + negate b
negate-addInt (pos a)       (pos b)       = neg-add a b
negate-addInt (pos zero)    (negsuc b)    = refl
negate-addInt (pos (suc a)) (negsuc b)    = negate-NZ (suc a) (suc b)
negate-addInt (negsuc a)    (pos zero)    = pos ∘ suc $≡ sym (add-zero-r a)
negate-addInt (negsuc a)    (pos (suc b)) = negate-NZ (suc b) (suc a)
negate-addInt (negsuc a)    (negsuc b)    = pos $≡ sym (add-suc-r (suc a) b)

negate-subInt : (a b : Int) → negate (a - b) ≡ b - a
negate-subInt a b = negate-addInt a (negate b) ⟨≡⟩
                    negate a +_ $≡ negate-idempotent b ⟨≡⟩
                    addInt-commute (negate a) b

--- Properties of subtraction ---

private
  diffNat-equal : ∀ a → diffNat a a ≡ 0
  diffNat-equal zero = refl
  diffNat-equal (suc a) = diffNat-equal a

subInt-equal : (a b : Int) → a ≡ b → a - b ≡ 0
subInt-equal (pos zero)    _ refl = refl
subInt-equal (pos (suc n)) _ refl = -NZ-spec (suc n) (suc n) ⟨≡⟩ diffNat-equal n
subInt-equal (negsuc n)    _ refl = -NZ-spec (suc n) (suc n) ⟨≡⟩ diffNat-equal n
