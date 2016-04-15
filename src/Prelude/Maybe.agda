
module Prelude.Maybe where

open import Prelude.Unit
open import Prelude.Empty
open import Prelude.Function
open import Prelude.Functor
open import Prelude.Applicative
open import Prelude.Monad
open import Prelude.Equality
open import Prelude.Decidable

data Maybe {a} (A : Set a) : Set a where
  nothing : Maybe A
  just    : A → Maybe A

{-# HASKELL type AgdaMaybe l = Maybe #-}
{-# COMPILED_DATA Maybe MAlonzo.Code.Prelude.Maybe.AgdaMaybe Nothing Just #-}

maybe : ∀ {a b} {A : Set a} {B : Set b} → B → (A → B) → Maybe A → B
maybe z f nothing  = z
maybe z f (just x) = f x

IsJust : ∀ {a} {A : Set a} → Maybe A → Set
IsJust = maybe ⊥ (const ⊤)

FromJust : ∀ {a} {A : Set a} → Maybe A → Set a
FromJust {A = A} = maybe ⊤′ (const A)

fromJust : ∀ {a} {A : Set a} (m : Maybe A) → FromJust m
fromJust nothing  = _
fromJust (just x) = x

maybeYes : ∀ {a} {A : Set a} → Dec A → Maybe A
maybeYes (yes x) = just x
maybeYes (no _)  = nothing

--- Equality ---

just-inj : ∀ {a} {A : Set a} {x y : A} → just x ≡ just y → x ≡ y
just-inj refl = refl

eqMaybe : ∀ {a} {A : Set a} {{EqA : Eq A}} (x y : Maybe A) → Dec (x ≡ y)
eqMaybe nothing nothing  = yes refl
eqMaybe nothing (just x) = no (λ ())
eqMaybe (just x) nothing = no (λ ())
eqMaybe (just x) (just y) with x == y
eqMaybe (just x) (just .x) | yes refl = yes refl
eqMaybe (just x) (just y)  | no  neq  = no (λ eq → neq (just-inj eq))

instance
  EqMaybe : ∀ {a} {A : Set a} {{EqA : Eq A}} → Eq (Maybe A)
  EqMaybe = record { _==_ = eqMaybe }

--- Monad ---

instance
  MonadMaybe : ∀ {a} → Monad {a} Maybe
  return {{MonadMaybe}}     = just
  _>>=_  {{MonadMaybe}} m f = maybe nothing f m

  MonadMaybe′ : ∀ {a b} → Monad′ {a} {b} Maybe
  _>>=′_ {{MonadMaybe′}} m f = maybe nothing f m

  FunctorMaybe : ∀ {a} → Functor (Maybe {a})
  FunctorMaybe = defaultMonadFunctor

  FunctorMaybe′ : ∀ {a b} → Functor′ {a} {b} Maybe
  fmap′ {{FunctorMaybe′}} f nothing  = nothing
  fmap′ {{FunctorMaybe′}} f (just x) = just (f x)

  ApplicativeMaybe : ∀ {a} → Applicative (Maybe {a})
  ApplicativeMaybe = defaultMonadApplicative

  ApplicativeMaybe′ : ∀ {a b} → Applicative′ {a} {b} Maybe
  _<*>′_ {{ApplicativeMaybe′}} (just f) (just x) = just (f x)
  _<*>′_ {{ApplicativeMaybe′}}  _        _       = nothing
