-- Evidence producing divmod.
module Data.Nat.DivMod where

open import Prelude
open import Control.WellFounded
open import Tactic.Nat
open import Tactic.Nat.Reflect
open import Tactic.Nat.Exp
open import Data.Nat.Properties

private
  lemCancelMinus : ∀ b → b - b ≡ 0
  lemCancelMinus zero    = refl
  lemCancelMinus (suc b) = lemCancelMinus b

  lemPlusMinus : ∀ a b → a + b - b ≡ a
  lemPlusMinus zero b = lemCancelMinus b
  lemPlusMinus (suc a) zero = auto
  lemPlusMinus (suc a) (suc b) =
    -- Want cong tactic for this!
    let lem : a + suc b - b ≡ suc a + b - b
        lem = cong (λ z → z - b) auto
    in lem ⟨≡⟩ lemPlusMinus (suc a) b

  lemModAux : ∀ k m n j → LessThan j n → modAux k m n j ≡ modAux 0 m (n - suc j) m
  lemModAux k m zero j (diff _ ())
  lemModAux k m (suc n) zero lt = refl
  lemModAux k m (suc n) (suc j) (diff d eq) =
    lemModAux (suc k) m n j
    $ diff d $ follows-from eq

  lemDivAux : ∀ k m n j → LessThan j n → divAux k m n j ≡ divAux (suc k) m (n - suc j) m
  lemDivAux k m zero j (diff _ ())
  lemDivAux k m (suc n) zero lt = refl
  lemDivAux k m (suc n) (suc j) (diff d eq) =
    lemDivAux k m n j
    $ diff d $ follows-from eq

  modLessAux : ∀ k m n j → LessThan (k + j) (suc m) → LessThan (modAux k m n j) (suc m)
  modLessAux k m zero j (diff d lt) =
    diff (j + d) $ lt ⟨≡⟩ auto
  modLessAux k m (suc n) zero _ =
    modLessAux 0 m n m $ diff 0 $ auto
  modLessAux k m (suc n) (suc j) (diff d lt) =
    modLessAux (suc k) m n j
    $ diff d $ follows-from lt

  LessThan′ : Nat → Nat → Set
  LessThan′ a b = b ≡ b - suc a + suc a

  toPrimed : ∀ {a b} → LessThan a b → LessThan′ a b
  toPrimed {a = a} (diff! k) rewrite lemPlusMinus k a = auto

  modLessAux′ : ∀ k m n j → LessThan (k + j) (suc m) → LessThan′ (modAux k m n j) (suc m)
  modLessAux′ k m n j lt = toPrimed (modLessAux k m n j lt)

  modLess : ∀ a b → LessThan (a mod suc b) (suc b)
  modLess a b = diff (b - a mod suc b) $ eraseEquality $
                follows-from (modLessAux′ 0 b a b (diff 0 auto))

  0≠1 : ∀ {a} {A : Set a} → 0 ≡ 1 → A
  0≠1 ()

  notLess1 : ∀ {a n} {A : Set a} → LessThan (suc n) 1 → A
  notLess1 (diff k eq) = 0≠1 (use eq tactic simpl | λ ())

  lessSuc-inj : ∀ {a b} → LessNat (suc a) (suc b) → LessNat a b
  lessSuc-inj (diff j eq) = diff j (follows-from eq)

  divAuxGt : ∀ k a b j → LessNat a (suc j) → divAux k b a j ≡ k
  divAuxGt k  zero   b  j      lt = refl
  divAuxGt k (suc a) b  zero   lt = notLess1 lt
  divAuxGt k (suc a) b (suc j) lt = divAuxGt k a b j (lessSuc-inj lt)

  modAuxGt : ∀ k a b j → LessNat a (suc j) → modAux k b a j ≡ k + a
  modAuxGt k zero b j lt = auto
  modAuxGt k (suc a) b  zero   lt = notLess1 lt
  modAuxGt k (suc a) b (suc j) lt = follows-from (modAuxGt (suc k) a b j (lessSuc-inj lt))

  divmodAux : ∀ k a b → Acc LessThan a → divAux k b a b * suc b + modAux 0 b a b ≡ k * suc b + a
  divmodAux k a b wf with compare b a
  ... | greater (diff j p)
        rewrite divAuxGt k a b b (diff (suc j) (cong suc p))
              | modAuxGt 0 a b b (diff (suc j) (cong suc p)) = refl
  divmodAux k a .a wf | equal refl
        rewrite divAuxGt k a a a (diff! 0)
              | modAuxGt 0 a a a (diff! 0) = refl
  divmodAux k .(suc (j + b)) b (acc wf) | less (diff! j)
    rewrite lemDivAux k b (suc (j + b)) b (diff! j)
          | lemModAux 0 b (suc (j + b)) b (diff! j)
          | lemPlusMinus j b
          = follows-from (divmodAux (suc k) j b (wf j (diff b auto)))

  divmod-spec : ∀ a b′ → let b = suc b′ in
                  a div b * b + a mod b ≡ a
  divmod-spec a b = eraseEquality (divmodAux 0 a b (wfNat a))

--- Public definitions ---

data DivMod a b : Set where
  qr : ∀ q r → LessThan r b → q * b + r ≡ a → DivMod a b

quot : ∀ {a b} → DivMod a b → Nat
quot (qr q _ _ _) = q

rem : ∀ {a b} → DivMod a b → Nat
rem (qr _ r _ _) = r

rem-less : ∀ {a b} (d : DivMod a b) → LessThan (rem d) b
rem-less (qr _ _ lt _) = lt

quot-rem-sound : ∀ {a b} (d : DivMod a b) → quot d * b + rem d ≡ a
quot-rem-sound (qr _ _ _ eq) = eq

syntax divMod b a = a divmod b
divMod : ∀ b {{_ : NonZero b}} a → DivMod a b
divMod zero {{}} a
divMod (suc b) a = qr (a div suc b) (a mod suc b) (modLess a b) (divmod-spec a b)

--- Properties ---

mod-less : ∀ b {{_ : NonZero b}} a → LessThan (a mod b) b
mod-less zero {{}} _
mod-less (suc b) a = rem-less (a divmod suc b)

divmod-sound : ∀ b {{_ : NonZero b}} a → (a div b) * b + a mod b ≡ a
divmod-sound zero {{}} _
divmod-sound (suc b) a = quot-rem-sound (a divmod suc b)

private
  divmod-unique′ : ∀ b q₁ q₂ r₁ r₂ → LessThan r₁ b → LessThan r₂ b → q₁ * b + r₁ ≡ q₂ * b + r₂ → q₁ ≡ q₂ × r₁ ≡ r₂
  divmod-unique′ b zero zero r₁ r₂ lt₁ lt₂ eq = refl , eq
  divmod-unique′ b zero (suc q₂) .(q₂ * b + b + r₂) r₂ (diff k eq) lt₂ refl =
    ⊥-elim (0≠suc (k + q₂ * b + r₂) (follows-from eq))
  divmod-unique′ b (suc q₁) zero r₁ .(q₁ * b + b + r₁) lt₁ (diff k eq) refl =
    ⊥-elim (0≠suc (k + q₁ * b + r₁) (follows-from eq))
  divmod-unique′ b (suc q₁) (suc q₂) r₁ r₂ lt₁ lt₂ eq =
    first (cong suc) $ divmod-unique′ b q₁ q₂ r₁ r₂ lt₁ lt₂ (follows-from eq)

divmod-unique : ∀ {a b} (d₁ d₂ : DivMod a b) → quot d₁ ≡ quot d₂ × rem d₁ ≡ rem d₂
divmod-unique (qr q₁ r₁ lt₁ eq₁) (qr q₂ r₂ lt₂ eq₂) =
  divmod-unique′ _ q₁ q₂ r₁ r₂ lt₁ lt₂ (eq₁ ⟨≡⟩ʳ eq₂)

quot-unique : ∀ {a b} (d₁ d₂ : DivMod a b) → quot d₁ ≡ quot d₂
quot-unique d₁ d₂ = fst (divmod-unique d₁ d₂)

rem-unique : ∀ {a b} (d₁ d₂ : DivMod a b) → rem d₁ ≡ rem d₂
rem-unique d₁ d₂ = snd (divmod-unique d₁ d₂)

--- Even/Odd ---

data Even n : Set where
  dbl : ∀ k → k * 2 ≡ n → Even n

data Odd n : Set where
  dbl+1 : ∀ k → 1 + k * 2 ≡ n → Odd n

parity : ∀ n → Either (Odd n) (Even n)
parity n with n divmod 2
parity n | qr q 0 lt eq = right $ dbl   q (follows-from eq)
parity n | qr q 1 lt eq = left  $ dbl+1 q (follows-from eq)
parity n | qr q (suc (suc _)) (diff _ bad) _ = 0≠1 $ use bad $ tactic simpl | λ ()

instance
  ShowDivMod : ∀ {a b} → Show (DivMod a b)
  ShowDivMod {a} {b} =
    record { showsPrec = λ { p (qr q r _ _) →
      showParen (p > 0) $ shows a ∘ showString " == "
                        ∘ shows q ∘ showString " * " ∘ shows b ∘ showString " + " ∘ shows r } }
