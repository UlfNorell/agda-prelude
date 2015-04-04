
module Data.Nat.BinarySearch where

open import Prelude
open import Data.Nat.Properties
open import Tactic.Nat
open import Control.WellFounded
open import Data.Nat.DivMod

data SearchResult! {a} (P : Nat → Set a) (lo hi : Nat) : Set a where
  here : ∀ k (!pk : ¬ P k) (psk : P (suc k)) (lo≤k : lo ≤ k) (k<hi : k < hi) → SearchResult! P lo hi

data SearchResult {a} (P : Nat → Set a) (lo hi : Nat) : Set a where
  here      : ∀ k (!pk : ¬ P k) (psk : P (suc k)) (lo≤k : lo ≤ k) (k<hi : k < hi) → SearchResult P lo hi
  below     : P lo → SearchResult P lo hi
  none      : ¬ P hi → SearchResult P lo hi
  bad-range : lo > hi → SearchResult P lo hi

private
  infixr 0 _⟨=⟩_
  _⟨=⟩_ : ∀ {a b c} → a ≡ b → b ≤ c → a ≤ c
  a=b ⟨=⟩ b≤c = diff 0 (cong suc (sym a=b)) ⟨≤⟩ b≤c

private
  lem-half : ∀ n → suc n div 2 < suc n
  lem-half n with suc n div 2 | suc n mod 2 | divmod-sound 2 (suc n)
  lem-half n | zero  | r | eq = diff n auto
  lem-half n | suc q | r | eq = diff (q + r) (follows-from (sym eq))

  lem-half-nonzero : ∀ n → NonZero ((2 + n) div 2)
  lem-half-nonzero n with (2 + n) div 2 | (2 + n) mod 2 | divmod-sound 2 (2 + n) | mod-less 2 (2 + n)
  lem-half-nonzero n | zero  | ._ | refl | diff k eq = refute eq
  lem-half-nonzero n | suc q | r  | _    | _         = _

  lem-upper : ∀ {lo hi d} d′ {{_ : NonZero d′}} →
              hi ≡ suc (d + lo) → hi - (d′ + lo) ≤ d
  lem-upper zero {{}}
  lem-upper {a} {._} {d} (suc d′) refl =
    cong (λ z → d + a - z) (add-commute d′ a)
    ⟨=⟩ sub-add-r (d + a) a d′
    ⟨=⟩ cong (_- d′) autosub
    ⟨=⟩ sub-leq d d′

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
                   (k<m ⟨<⟩ transport (λ z → d′ + lo < z) (sym eq)
                             (plus-monotone-l lo d′<d))
         }
     ; (no !pm) →
         let m≤hi : m ≤ hi
             m≤hi = plus-monotone-l lo d′<d ⟨≤⟩ diff 1 (cong suc eq)
             d′≠0 : NonZero d′
             d′≠0 = lem-half-nonzero d₀
             hi-m≤d : hi - m ≤ d
             hi-m≤d = lem-upper d′ eq
             eq : hi ≡ hi - m + m
             eq = eraseEquality (sym (sub-less m≤hi))
         in
         case search m hi (hi - m) eq (wf (hi - m) hi-m≤d) check !pm phi of λ
         { (here k !pk psk m≤k k<hi) → here k !pk psk (leq-add-l d′ ⟨≤⟩ m≤k) k<hi }
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
