
module Numeric.Nat.BinarySearch where

open import Prelude
open import Numeric.Nat.Properties
open import Tactic.Nat.Prelude
open import Control.WellFounded
open import Numeric.Nat.DivMod

data SearchResult! {a} (P : Nat → Set a) (lo hi : Nat) : Set a where
  here : ∀ k (!pk : ¬ P k) (psk : P (suc k)) (lo≤k : lo ≤ k) (k<hi : k < hi) → SearchResult! P lo hi

data SearchResult {a} (P : Nat → Set a) (lo hi : Nat) : Set a where
  here      : ∀ k (!pk : ¬ P k) (psk : P (suc k)) (lo≤k : lo ≤ k) (k<hi : k < hi) → SearchResult P lo hi
  below     : P lo → SearchResult P lo hi
  none      : ¬ P hi → SearchResult P lo hi
  bad-range : lo > hi → SearchResult P lo hi

private
  infixr 0 _⟨=<⟩_ _⟨<=⟩_
  _⟨=<⟩_ : ∀ {a : Nat} {b c} → a ≡ b → b < c → a < c
  refl ⟨=<⟩ b<c = b<c

  _⟨<=⟩_ : ∀ {a : Nat} {b c} → a < b → b ≡ c → a < c
  a<b ⟨<=⟩ refl = a<b

private
  lem-half : ∀ n → suc n div 2 < suc n
  lem-half n with suc n div 2 | suc n mod 2 | divmod-sound 2 (suc n)
  lem-half n | zero  | r | eq = auto
  lem-half n | suc q | r | eq = by eq

  lem-half-nonzero : ∀ n → NonZero ((2 + n) div 2)
  lem-half-nonzero n with (2 + n) div 2 | (2 + n) mod 2 | divmod-sound 2 (2 + n) | mod-less 2 (2 + n)
  lem-half-nonzero n | zero  | ._ | refl | lt = refute lt
  lem-half-nonzero n | suc q | r  | _    | _  = _

  lem-upper : ∀ {lo hi d} d′ {{_ : NonZero d′}} →
              hi ≡ suc (d + lo) → hi - (d′ + lo) ≤ d
  lem-upper zero {{}}
  lem-upper {d = d} (suc d′) refl = by (sub-leq d d′)

  search : ∀ {a} {P : Nat → Set a} lo hi d → hi ≡ d + lo → Acc _<_ d →
             (∀ n → Dec (P n)) →
             ¬ P lo → P hi → SearchResult! P lo hi
  search lo .lo 0 refl wf check !plo phi = ⊥-elim (!plo phi)
  search lo .(suc lo) 1 refl wf check !plo phi = here lo !plo phi (diff! 0) (diff! 0)
  search lo hi (suc (suc d₀)) eq (acc wf) check !plo phi =
    let d = suc d₀
        d′ = suc d div 2
        m = d′ + lo
        d′<d : d′ < suc d
        d′<d = lem-half d in
    case check m of λ
     { (yes pm) →
         case search lo m d′ refl (wf _ d′<d) check !plo pm of λ
         { (here k !pk psk lo≤k k<m) → here k !pk psk lo≤k $
             k<m ⟨<⟩ by d′<d ⟨<=⟩ sym eq
         }
     ; (no !pm) →
         let m≤hi : m ≤ hi
             m≤hi = by d′<d ⟨≤⟩ diff 1 (cong suc eq)
             instance d′≠0 : NonZero d′
                      d′≠0 = lem-half-nonzero d₀
             eq′ : hi ≡ hi - m + m
             eq′ = eraseEquality (sym (sub-less m≤hi))
         in
         case search m hi (hi - m) eq′ (wf (hi - m) (lem-upper d′ eq)) check !pm phi of λ
         { (here k !pk psk m≤k k<hi) → here k !pk psk (auto ⟨≤⟩ m≤k) k<hi }
     }

private
  unbang : ∀ {a} {P : Nat → Set a} {lo hi} → SearchResult! P lo hi → SearchResult P lo hi
  unbang (here k x x₁ x₂ x₃) = here k x x₁ x₂ x₃

binarySearch : ∀ {a} {P : Nat → Set a} lo hi →
                 (∀ n → Dec (P n)) →
                 SearchResult P lo hi
binarySearch lo hi check with compare lo hi
... | greater lo>hi = bad-range lo>hi
binarySearch lo .lo check | equal refl =
  case check lo of λ
  { (yes p) → below p
  ; (no !p) → none !p
  }
binarySearch lo ._ check | less (diff! d) =
  let hi = suc d + lo in
  case check lo of λ
  { (yes p) → below p
  ; (no !p) →
    case check hi of λ
    { (yes p) → unbang $ search lo hi (suc d) refl (wfNat (suc d)) check !p p
    ; (no !p) → none !p }
  }
