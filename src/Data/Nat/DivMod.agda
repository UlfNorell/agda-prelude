-- Evidence producing divmod.
module Data.Nat.DivMod where

open import Prelude
open import Control.WellFounded
open import Tactic.Nat
open import Tactic.Nat.Reflect
open import Tactic.Nat.Exp
open import Data.Nat.Properties

private
  lemModAux′ : ∀ k m b j → modAux k m (suc j + b) j ≡ modAux 0 m b m
  lemModAux′ k m b  zero   = refl
  lemModAux′ k m b (suc j) = lemModAux′ (suc k) m b j

  lemModAux : ∀ k m b j → modAux k m (suc b + j) j ≡ modAux 0 m b m
  lemModAux k m b j = (λ z → modAux k m (suc z) j) $≡ auto ⟨≡⟩ lemModAux′ k m b j

  lemDivAux′ : ∀ k m b j → divAux k m (suc j + b) j ≡ divAux (suc k) m b m
  lemDivAux′ k m b  zero   = refl
  lemDivAux′ k m b (suc j) = lemDivAux′ k m b j

  lemDivAux : ∀ k m b j → divAux k m (suc b + j) j ≡ divAux (suc k) m b m
  lemDivAux k m b j = (λ z → divAux k m (suc z) j) $≡ auto ⟨≡⟩ lemDivAux′ k m b j

  modLessAux : ∀ k m n j → k + j < suc m → modAux k m n j < suc m
  modLessAux k m  zero    j      lt = by lt
  modLessAux k m (suc n)  zero   _  = modLessAux 0 m n m auto
  modLessAux k m (suc n) (suc j) lt = modLessAux (suc k) m n j (by lt)

  modLess : ∀ a b → a mod suc b < suc b
  modLess a b = fast-diff $ modLessAux 0 b a b auto

  divAuxGt : ∀ k a b j → a ≤ j → divAux k b a j ≡ k
  divAuxGt k  zero   b  j      lt = refl
  divAuxGt k (suc a) b  zero   lt = refute lt
  divAuxGt k (suc a) b (suc j) lt = divAuxGt k a b j (by lt)

  modAuxGt : ∀ k a b j → a ≤ j → modAux k b a j ≡ k + a
  modAuxGt k  zero   b  j      lt = auto
  modAuxGt k (suc a) b  zero   lt = refute lt
  modAuxGt k (suc a) b (suc j) lt = by (modAuxGt (suc k) a b j (by lt))

  qr-mul : (b q r : Nat) → Nat
  qr-mul b q r = q * suc b + r

  divmodAux : ∀ k a b → Acc _<_ a → qr-mul b (divAux k b a b) (modAux 0 b a b) ≡ qr-mul b k a
  divmodAux k a  b wf    with compare b a
  divmodAux k a  b wf       | greater lt =
    let leq : a ≤ b
        leq = by lt in
    qr-mul b $≡ divAuxGt k a b b leq
             *≡ modAuxGt 0 a b b leq
  divmodAux k a .a wf       | equal refl =
    qr-mul a $≡ divAuxGt k a a a (diff! 0)
             *≡ modAuxGt 0 a a a (diff! 0)
  divmodAux k ._ b (acc wf) | less (diff! j) =
    qr-mul b $≡ lemDivAux k b j b *≡ lemModAux 0 b j b ⟨≡⟩
    by (divmodAux (suc k) j b (wf j auto))

  divmod-spec : ∀ a b′ → let b = suc b′ in a div b * b + a mod b ≡ a
  divmod-spec a b = eraseEquality (divmodAux 0 a b (wfNat a))

--- Public definitions ---

data DivMod (a b : Nat) : Set where
  qr : ∀ q r → r < b → q * b + r ≡ a → DivMod a b

quot : ∀ {a b} → DivMod a b → Nat
quot (qr q _ _ _) = q

rem : ∀ {a b} → DivMod a b → Nat
rem (qr _ r _ _) = r

rem-less : ∀ {a b} (d : DivMod a b) → rem d < b
rem-less (qr _ _ lt _) = lt

quot-rem-sound : ∀ {a b} (d : DivMod a b) → quot d * b + rem d ≡ a
quot-rem-sound (qr _ _ _ eq) = eq

syntax divMod b a = a divmod b
divMod : ∀ b {{_ : NonZero b}} a → DivMod a b
divMod zero {{}} a
divMod (suc b) a = qr (a div suc b) (a mod suc b) (modLess a b) (divmod-spec a b)

{-# INLINE divMod #-}

--- Properties ---

mod-less : ∀ b {{_ : NonZero b}} a → a mod b < b
mod-less zero {{}} _
mod-less (suc b) a = rem-less (a divmod suc b)

divmod-sound : ∀ b {{_ : NonZero b}} a → (a div b) * b + a mod b ≡ a
divmod-sound zero {{}} _
divmod-sound (suc b) a = quot-rem-sound (a divmod suc b)

private
  divmod-unique′ : (b q₁ q₂ r₁ r₂ : Nat) → r₁ < b → r₂ < b → q₁ * b + r₁ ≡ q₂ * b + r₂ → q₁ ≡ q₂ × r₁ ≡ r₂
  divmod-unique′ b  zero     zero    r₁ r₂ lt₁ lt₂ eq   = refl , eq
  divmod-unique′ b  zero    (suc q₂) ._ r₂ lt₁ lt₂ refl = refute lt₁
  divmod-unique′ b (suc q₁)  zero    r₁ ._ lt₁ lt₂ refl = refute lt₂
  divmod-unique′ b (suc q₁) (suc q₂) r₁ r₂ lt₁ lt₂ eq   =
    first (cong suc) $ divmod-unique′ b q₁ q₂ r₁ r₂ lt₁ lt₂ (by eq)

divmod-unique : ∀ {a b} (d₁ d₂ : DivMod a b) → quot d₁ ≡ quot d₂ × rem d₁ ≡ rem d₂
divmod-unique (qr q₁ r₁ lt₁ eq₁) (qr q₂ r₂ lt₂ eq₂) =
  case divmod-unique′ _ q₁ q₂ r₁ r₂ lt₁ lt₂ (eq₁ ⟨≡⟩ʳ eq₂) of
  λ p → eraseEquality (fst p) , eraseEquality (snd p)

quot-unique : ∀ {a b} (d₁ d₂ : DivMod a b) → quot d₁ ≡ quot d₂
quot-unique d₁ d₂ = fst (divmod-unique d₁ d₂)

rem-unique : ∀ {a b} (d₁ d₂ : DivMod a b) → rem d₁ ≡ rem d₂
rem-unique d₁ d₂ = snd (divmod-unique d₁ d₂)

instance
  ShowDivMod : ∀ {a b} → Show (DivMod a b)
  ShowDivMod {a} {b} =
    record { showsPrec = λ { p (qr q r _ _) →
      showParen (p >? 0) $ shows a ∘ showString " == "
                         ∘ shows q ∘ showString " * " ∘ shows b ∘ showString " + " ∘ shows r } }
