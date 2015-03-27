
module Data.Nat.Properties where

open import Prelude
open import Data.Nat.Properties.Core public
open import Tactic.Nat

--- LessNat ---

less-trans : ∀ {x y z} → LessNat x y → LessNat y z → LessNat x z
less-trans (diff! a) (diff! b) = diff (suc (b + a)) auto

less-zero : ∀ {a b} → LessThan a b → LessThan 0 b
less-zero {a} (diff! k) = diff (k + a) auto

less-suc : {a b : Nat} → LessThan a b → LessThan a (suc b)
less-suc (diff k eq) = diff (suc k) (cong suc eq)

less-suc-l : ∀ {a b : Nat} → LessThan (suc a) b → LessThan a b
less-suc-l (diff k eq) = diff (suc k) (follows-from eq)

less-zero-suc : ∀ {a} → LessThan 0 (suc a)
less-zero-suc {a} = diff a auto

less-antirefl : ∀ {a b : Nat} → LessThan a b → ¬ (a ≡ b)
less-antirefl (diff! k) eq = 0≠suc k (follows-from eq)

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


