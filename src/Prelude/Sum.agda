
module Prelude.Sum where

open import Agda.Primitive
open import Prelude.Empty
open import Prelude.Unit
open import Prelude.List
open import Prelude.Functor
open import Prelude.Applicative
open import Prelude.Monad
open import Prelude.Equality
open import Prelude.Decidable
open import Prelude.Product
open import Prelude.Function

data Either {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  left  : A → Either A B
  right : B → Either A B

{-# IMPORT Agda.FFI #-}
{-# COMPILED_DATA Either Agda.FFI.AgdaEither Left Right #-}

either : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
           (A → C) → (B → C) → Either A B → C
either f g (left  x) = f x
either f g (right x) = g x

lefts : ∀ {a b} {A : Set a} {B : Set b} → List (Either A B) → List A
lefts = concatMap λ { (left x) → [ x ]; (right _) → [] }

rights : ∀ {a b} {A : Set a} {B : Set b} → List (Either A B) → List B
rights = concatMap λ { (left _) → []; (right x) → [ x ] }

partitionMap : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
                 (A → Either B C) → List A → List B × List C
partitionMap f [] = [] , []
partitionMap f (x ∷ xs) = either (first ∘ _∷_)
                                 (λ y → second (_∷_ y))  -- second ∘ _∷_ doesn't work for some reason
                                 (f x) (partitionMap f xs)

--- Equality ---

left-inj : ∀ {a} {A : Set a} {x y : A} {b} {B : Set b} →
           left {B = B} x ≡ left y → x ≡ y
left-inj refl = refl

right-inj : ∀ {b} {B : Set b} {x y : B} {a} {A : Set a} →
            right {A = A} x ≡ right y → x ≡ y
right-inj refl = refl

eqEither : ∀ {a b} {A : Set a} {B : Set b} {{EqA : Eq A}} {{EqB : Eq B}}
             (x y : Either A B) → Dec (x ≡ y)
eqEither (left x)  (right y) = no (λ ())
eqEither (right x) (left y)  = no (λ ())
eqEither (left x)  (left y)  with x == y
eqEither (left x) (left .x)     | yes refl = yes refl
eqEither (left x) (left y)      | no neq   = no λ eq → neq (left-inj eq)
eqEither (right x) (right y) with x == y
eqEither (right x) (right .x)   | yes refl = yes refl
eqEither (right x) (right y)    | no neq   = no λ eq → neq (right-inj eq)

EqEither : ∀ {a b} {A : Set a} {B : Set b} {{EqA : Eq A}} {{EqB : Eq B}} →
              Eq (Either A B)
EqEither = record { _==_ = eqEither }

--- Monad instance ---

MonadEither : ∀ {a b} {A : Set a} → Monad (Either {b = b} A)
MonadEither = record { return = right
                     ; _>>=_  = λ m f → either left f m }

FunctorEither : ∀ {a b} {A : Set a} → Functor (Either {b = b} A)
FunctorEither = defaultMonadFunctor

ApplicativeEither : ∀ {a b} {A : Set a} → Applicative (Either {b = b} A)
ApplicativeEither = defaultMonadApplicative
