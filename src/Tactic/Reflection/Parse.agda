
module Tactic.Reflection.Parse where

open import Prelude
open import Control.Monad.State
open import Control.Monad.Zero
open import Builtin.Reflection
open import Tactic.Reflection.Equality

ParseTerm : Set → Set
ParseTerm = StateT (Nat × List (Term × Nat)) Maybe

infixr 0 _catch_
_catch_ : ∀ {A} → ParseTerm A → ParseTerm A → ParseTerm A
m catch h = stateT (λ s → maybe (runStateT h s) just (runStateT m s))

parseTerm : ∀ {A} → ParseTerm A → Maybe (A × List Term)
parseTerm r =
  second (reverse ∘ map fst ∘ snd) <$>
  runStateT r (0 , [])

fresh : Term → ParseTerm Nat
fresh t =
  get >>= uncurry′ λ i Γ →
  i <$ put (suc i , (t , i) ∷ Γ)

atom : Term → ParseTerm Nat
atom v = maybe (fresh v) pure =<< gets (flip lookup v ∘ snd)
