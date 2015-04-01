
module Data.Nat.Properties where

open import Prelude
open import Prelude.Equality.Unsafe using (safeEqual)
open import Data.Nat.Properties.Core public
open import Tactic.Nat

--- Subtraction ---

cancel-sub : ∀ b → b - b ≡ 0
cancel-sub zero    = refl
cancel-sub (suc b) = cancel-sub b

cancel-add-sub : ∀ a b → a + b - b ≡ a
cancel-add-sub zero b = cancel-sub b
cancel-add-sub (suc a) zero = auto
cancel-add-sub (suc a) (suc b) =
  -- Want cong tactic for this!
  let lem : a + suc b - b ≡ suc a + b - b
      lem = cong (λ z → z - b) auto
  in lem ⟨≡⟩ cancel-add-sub (suc a) b

sub-0-l : ∀ n → 0 - n ≡ 0
sub-0-l zero = refl
sub-0-l (suc n) = refl

sub-add-r : ∀ a b c → a - (b + c) ≡ a - b - c
sub-add-r a zero c = refl
sub-add-r zero b c rewrite sub-0-l (b + c) | sub-0-l b | sub-0-l c = refl
sub-add-r (suc a) (suc b) c = sub-add-r a b c

sub-mul-distr-l : ∀ a b c → (a - b) * c ≡ a * c - b * c
sub-mul-distr-l zero b c rewrite sub-0-l b | sub-0-l (b * c) = refl
sub-mul-distr-l (suc a) zero c = refl
sub-mul-distr-l (suc a) (suc b) c rewrite sub-mul-distr-l a b c =
  a * c - b * c
    ≡⟨ cong (_- (b * c)) (cancel-add-sub _ c) ⟩ʳ
  a * c + c - c - b * c
    ≡⟨ sub-add-r (a * c + c) c (b * c) ⟩ʳ
  a * c + c - (c + b * c)
    ≡⟨ cong ((a * c + c) -_) (add-commute c (b * c)) ⟩
  a * c + c - (b * c + c) ∎

sub-less : ∀ {a b} → LessThan a b → b - suc a + suc a ≡ b
sub-less {a} (diff! k) = cong (_+ suc a) (cancel-add-sub k a) ⟨≡⟩ auto

--- LessNat ---

fast-diff : ∀ {a b} → LessNat a b → LessNat a b
fast-diff {a} {b} a<b = diff (b - suc a) (safeEqual (sub-less a<b ʳ⟨≡⟩ auto))

_⟨<⟩_ : ∀ {x y z} → LessNat x y → LessNat y z → LessNat x z
diff! a ⟨<⟩ diff! b = diff (suc (b + a)) auto

less-zero : ∀ {a b} → LessThan a b → LessThan 0 b
less-zero {a} (diff! k) = diff (k + a) auto

less-suc : {a b : Nat} → LessThan a b → LessThan a (suc b)
less-suc (diff k eq) = diff (suc k) (cong suc eq)

less-suc-l : ∀ {a b : Nat} → LessThan (suc a) b → LessThan a b
less-suc-l (diff k eq) = diff (suc k) (follows-from eq)

suc-monotone : ∀ {a b : Nat} → a [<] b → Nat.suc a [<] suc b
suc-monotone (diff k eq) = diff k (follows-from eq)

suc-monotoneʳ : ∀ {a b : Nat} → Nat.suc a [<] suc b → a [<] b
suc-monotoneʳ (diff k eq) = diff k (follows-from eq)

less-zero-suc : ∀ {a} → LessThan 0 (suc a)
less-zero-suc {a} = diff a auto

less-antirefl : ∀ {a b : Nat} → LessThan a b → ¬ (a ≡ b)
less-antirefl (diff! k) eq = 0≠suc k (follows-from eq)

less-raa : {a b : Nat} → ¬ (suc a [>] b) → a [<] b
less-raa {a} {b} a≱b with compare a b
less-raa a≱b | less    a<b = a<b
less-raa a≱b | equal  refl = ⊥-elim (a≱b (diff! 0))
less-raa a≱b | greater a>b = ⊥-elim (a≱b (less-suc a>b))

LessEq : (a b : Nat) → Set
LessEq a b = LessNat a (suc b)

infix 4 _[≤]_ _[≥]_
_[≤]_ = LessEq
_[≥]_ = flip LessEq

_⟨≤⟩_ : ∀ {a b c} → LessEq a b → LessEq b c → LessEq a c
diff! k ⟨≤⟩ diff! k₁ = diff (k₁ + k) auto

plus-zero-l : ∀ a b → a + b ≡ 0 → a ≡ 0
plus-zero-l zero b eq = refl
plus-zero-l (suc a) b eq = ⊥-elim (0≠suc (a + b) (sym eq))

plus-zero-r : ∀ a b → a + b ≡ 0 → b ≡ 0
plus-zero-r zero    b eq = eq
plus-zero-r (suc a) b eq = ⊥-elim (0≠suc (a + b) (sym eq))

leq-antisym : ∀ {a b} → a [≤] b → b [≤] a → a ≡ b
leq-antisym (diff! k) (diff k₁ eq) = use eq $ tactic simpl | (λ eq → sym (plus-zero-r k₁ k (sym eq))) 

leq-add-l : ∀ a {b} → LessEq b (a + b)
leq-add-l a {b} = diff! a

leq-add-r : ∀ {a} b → LessEq a (a + b)
leq-add-r {a} b = diff b auto

private
  less-mul-r′ : ∀ {a b : Nat} → NonZero b → LessEq a (a * b)
  less-mul-r′ {b = zero} ()
  less-mul-r′ {zero}  nz = diff! 0
  less-mul-r′ {suc a} {suc b} _ =
    let H : LessEq a (a * suc b + b)
        H = less-mul-r′ {a} {suc b} _ ⟨≤⟩ leq-add-r b
    in suc-monotone (transport (LessNat a) auto H)

less-mul-r : ∀ {a} b {{_ : NonZero b}} → LessEq a (a * b)
less-mul-r b = fast-diff (less-mul-r′ {b = b} it)


