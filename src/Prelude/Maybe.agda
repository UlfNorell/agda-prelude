
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

{-# FOREIGN GHC type AgdaMaybe l = Maybe #-}
{-# COMPILE GHC Maybe = data MAlonzo.Code.Prelude.Maybe.AgdaMaybe (Nothing | Just) #-}

maybe : ∀ {a b} {A : Set a} {B : Set b} → B → (A → B) → Maybe A → B
maybe z f nothing  = z
maybe z f (just x) = f x
{-# INLINE maybe #-}

fromMaybe : ∀ {a} {A : Set a} → A → Maybe A → A
fromMaybe z = maybe z id
{-# INLINE fromMaybe #-}

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

instance
  EqMaybe : ∀ {a} {A : Set a} {{EqA : Eq A}} → Eq (Maybe A)
  _==_ {{EqMaybe}} nothing nothing  = yes refl
  _==_ {{EqMaybe}} nothing (just x) = no λ ()
  _==_ {{EqMaybe}} (just x) nothing = no λ ()
  _==_ {{EqMaybe}} (just x) (just y) with x == y
  ... | yes eq  = yes (just $≡ eq)
  ... | no  neq = no (λ eq → neq (just-inj eq))

--- Monad ---

instance
  FunctorMaybe : ∀ {a} → Functor (Maybe {a})
  fmap {{FunctorMaybe}} f m = maybe nothing (just ∘ f) m

  ApplicativeMaybe : ∀ {a} → Applicative (Maybe {a})
  pure  {{ApplicativeMaybe}} = just
  _<*>_ {{ApplicativeMaybe}} mf mx = maybe nothing (λ f → fmap f mx) mf

  MonadMaybe : ∀ {a} → Monad {a} Maybe
  _>>=_  {{MonadMaybe}} m f = maybe nothing f m

  FunctorMaybe′ : ∀ {a b} → Functor′ {a} {b} Maybe
  fmap′ {{FunctorMaybe′}} f m = maybe nothing (just ∘ f) m

  ApplicativeMaybe′ : ∀ {a b} → Applicative′ {a} {b} Maybe
  _<*>′_ {{ApplicativeMaybe′}} (just f) (just x) = just (f x)
  _<*>′_ {{ApplicativeMaybe′}}  _        _       = nothing

  MonadMaybe′ : ∀ {a b} → Monad′ {a} {b} Maybe
  _>>=′_ {{MonadMaybe′}} m f = maybe nothing f m
