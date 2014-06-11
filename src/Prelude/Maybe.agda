
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

{-# IMPORT Agda.FFI #-}
{-# COMPILED_DATA Maybe Agda.FFI.AgdaMaybe Nothing Just #-}

maybe : ∀ {a b} {A : Set a} {B : Set b} → B → (A → B) → Maybe A → B
maybe z f nothing  = z
maybe z f (just x) = f x

IsJust : ∀ {a} {A : Set a} → Maybe A → Set
IsJust = maybe ⊥ (const ⊤)

fromJust : ∀ {a} {A : Set a} (m : Maybe A) {j : IsJust m} → A
fromJust nothing {}
fromJust (just x) = x

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

EqMaybe : ∀ {a} {A : Set a} {{EqA : Eq A}} → Eq (Maybe A)
EqMaybe = record { _==_ = eqMaybe }

--- Monad ---

MonadMaybe : ∀ {a} → Monad (Maybe {a})
MonadMaybe = record { return = just ; _>>=_ = flip (maybe nothing) }

FunctorMaybe : ∀ {a} → Functor (Maybe {a})
FunctorMaybe = defaultMonadFunctor

ApplicativeMaybe : ∀ {a} → Applicative (Maybe {a})
ApplicativeMaybe = defaultMonadApplicative
