
module Data.Nat.Properties where

open import Prelude
open import Data.Nat.Properties.Core public
open import Tactic.Nat

--- Subtraction ---

sub-add-r : ∀ a b c → a - (b + c) ≡ a - b - c
sub-add-r  a       zero   c = refl
sub-add-r  zero    b      c = autosub
sub-add-r (suc a) (suc b) c = sub-add-r a b c

sub-mul-distr-l : ∀ a b c → (a - b) * c ≡ a * c - b * c
sub-mul-distr-l zero b c = autosub
sub-mul-distr-l (suc a) zero c = refl
sub-mul-distr-l (suc a) (suc b) c = sub-mul-distr-l a b c ⟨≡⟩ autosub

sub-less : ∀ {a b} → a ≤ b → b - a + a ≡ b
sub-less {zero} _ = auto
sub-less {suc a} (diff! k) = autosub

sub-underflow : ∀ a b → a ≤ b → a - b ≡ 0
sub-underflow a ._ (diff! k) = autosub

sub-leq : ∀ a b → a - b ≤ a
sub-leq a b with compare a b
sub-leq a ._ | less    (diff! k) = diff a autosub
sub-leq a .a | equal    refl     = diff a autosub
sub-leq ._ b | greater (diff! k) = diff b autosub

--- LessNat ---

suc-monotone : ∀ {a b : Nat} → a < b → Nat.suc a < suc b
suc-monotone (diff k eq) = diff k (follows-from eq)

suc-monotoneʳ : ∀ {a b : Nat} → Nat.suc a < suc b → a < b
suc-monotoneʳ (diff k eq) = diff k (follows-from eq)

fast-diff : ∀ {a b} → LessNat a b → LessNat a b
fast-diff {a} {b} a<b = diff (b - suc a) (eraseEquality (sub-less (suc-monotone a<b) ʳ⟨≡⟩ auto))

infixr 0 _⟨<⟩_ _⟨≤⟩_

_⟨<⟩_ : ∀ {x y z} → LessNat x y → LessNat y z → LessNat x z
diff! a ⟨<⟩ diff! b = diff (suc (b + a)) auto

less-zero : ∀ {a b} → a < b → 0 < b
less-zero {a} (diff! k) = diff (k + a) auto

less-suc : {a b : Nat} → a < b → a < suc b
less-suc (diff k eq) = diff (suc k) (cong suc eq)

less-suc-l : ∀ {a b : Nat} → suc a < b → a < b
less-suc-l (diff k eq) = diff (suc k) (follows-from eq)

less-zero-suc : ∀ {a} → 0 < suc a
less-zero-suc {a} = diff a auto

less-antirefl : ∀ {a b : Nat} → a < b → ¬ (a ≡ b)
less-antirefl (diff! k) eq = refute eq

less-antisym : ∀ {a b : Nat} → a < b → b < a → ⊥
less-antisym (diff! k) (diff k₁ eq) = refute eq

less-not-geq : ∀ {a b : Nat} → a < b → b ≤ a → ⊥
less-not-geq (diff d eq) (diff! d₁) = refute eq

less-raa : {a b : Nat} → ¬ (suc a > b) → a < b
less-raa {a} {b} a≱b with compare a b
less-raa a≱b | less    a<b = a<b
less-raa a≱b | equal  refl = ⊥-elim (a≱b (diff! 0))
less-raa a≱b | greater a>b = ⊥-elim (a≱b (less-suc a>b))

_⟨≤⟩_ : {a b c : Nat} → a ≤ b → b ≤ c → a ≤ c
diff! k ⟨≤⟩ diff! k₁ = diff (k₁ + k) auto

plus-zero-l : ∀ a b → a + b ≡ 0 → a ≡ 0
plus-zero-l zero b eq = refl
plus-zero-l (suc a) b eq = refute eq

plus-zero-r : ∀ a b → a + b ≡ 0 → b ≡ 0
plus-zero-r zero    b eq = eq
plus-zero-r (suc a) b eq = refute eq

plus-monotone-l : ∀ {a b} c → a < b → a + c < b + c
plus-monotone-l c (diff k eq) = diff k (follows-from eq)

plus-monotone-r : ∀ a {b c} → b < c → a + b < a + c
plus-monotone-r a (diff k eq) = diff k (follows-from eq)

leq-antisym : {a b : Nat} → a ≤ b → b ≤ a → a ≡ b
leq-antisym (diff! k) (diff k₁ eq) = simplify eq to eq′ $ sym $ plus-zero-r k₁ k (sym eq′)

leq-add-l : ∀ a {b} → b ≤ a + b
leq-add-l a {b} = diff! a

leq-add-r : ∀ {a} b → a ≤ a + b
leq-add-r {a} b = diff b auto

private
  less-mul-r′ : ∀ a b → NonZero b → a ≤ a * b
  less-mul-r′ _ zero ()
  less-mul-r′ zero _ nz = diff! 0
  less-mul-r′ (suc a) (suc b) _ =
    let H : a ≤ a * suc b + b
        H = less-mul-r′ a (suc b) _ ⟨≤⟩ leq-add-r b
    in suc-monotone (transport (_<_ a) auto H)

less-mul-r : ∀ {a} b {{_ : NonZero b}} → a ≤ a * b
less-mul-r b = fast-diff (less-mul-r′ _ b it)


