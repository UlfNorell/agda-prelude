
module Numeric.Nat.Divide where

open import Prelude
open import Control.WellFounded
open import Numeric.Nat.Properties
open import Numeric.Nat.DivMod
open import Tactic.Nat

--- Divides predicate ---

data _Divides_ (a b : Nat) : Set where
  factor : ∀ q (eq : q * a ≡ b) → a Divides b

pattern factor! q = factor q refl

get-factor : ∀ {a b} → a Divides b → Nat
get-factor (factor q _) = q

dividesToDivMod : ∀ {a b} {{_ : NonZero b}} → b Divides a → DivMod a b
dividesToDivMod {b = zero } {{}}
dividesToDivMod {b = suc b} (factor q eq) = qr q 0 auto (by eq)

mod-divides : ∀ {a b} {{_ : NonZero a}} → a Divides b → b mod a ≡ 0
mod-divides {zero} {{}}
mod-divides {suc a} {b} (factor q eq) =
  rem-unique (b divmod suc a) (dividesToDivMod (factor q eq))

div-divides : ∀ {a b} {{_ : NonZero a}} → a Divides b → (b div a) * a ≡ b
div-divides {a} {b} a|b with divmod-sound a b
... | eq rewrite mod-divides a|b = by eq

private
  safediv : Nat → Nat → Nat
  safediv a 0 = 0
  safediv a (suc b) = a div suc b

  divides-safediv : ∀ {a b} → a Divides b → safediv b a * a ≡ b
  divides-safediv {zero } (factor! _) = auto
  divides-safediv {suc a} a|b = div-divides a|b

fast-divides : ∀ {a b} → a Divides b → a Divides b
fast-divides {a} {b} a|b = factor (safediv b a) (eraseEquality (divides-safediv a|b))

private
  no-divides-suc-mod : ∀ {a b} q {r} → LessNat (suc r) a → q * a + suc r ≡ b → ¬ (a Divides b)
  no-divides-suc-mod {zero} _ (diff _ ())
  no-divides-suc-mod {suc a} q {r} lt eq (factor q′ eq′) =
    refute (rem-unique
              (dividesToDivMod (factor q′ eq′))
              (qr q (suc r) lt eq))

  no-divides-zero : ∀ {a} → ¬ (0 Divides suc a)
  no-divides-zero {a} (factor q eq) = refute eq

_divides?_ : ∀ a b → Dec (a Divides b)
a     divides? zero  = yes (factor! 0)
zero  divides? suc b = no no-divides-zero
suc a divides? suc b with suc b divmod suc a
suc a divides? suc b | qr q  zero    _ eq  = yes (factor q (by eq))
suc a divides? suc b | qr q (suc r) lt eq₁ = no (no-divides-suc-mod q lt eq₁)

--- Instances ---

instance
  SmashDivides : ∀ {a b} {{_ : NonZero a}} → Smashed (a Divides b)
  SmashDivides {0} {{}}
  smashed {{SmashDivides {a@(suc _)}}} {factor q eq} {factor q₁ refl} =
    case mul-inj₁ q q₁ (suc _) eq of λ where refl → factor q $≡ smashed
