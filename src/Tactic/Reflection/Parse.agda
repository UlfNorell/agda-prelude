
module Tactic.Reflection.Parse where

open import Prelude
open import Control.Monad.State
open import Control.Monad.Zero
open import Builtin.Reflection
open import Tactic.Reflection.Equality
open import Data.Traversable

ParseTerm : (Set → Set) → Set → Set
ParseTerm M = StateT (Nat × List (Term × Nat)) M

module _ {M : Set → Set} {{_ : Functor M}} {{_ : Monad M}} where

  runParse : ∀ {A} → ParseTerm M A → M (A × List Term)
  runParse r =
    second (reverse ∘ map fst ∘ snd) <$>
    runStateT r (0 , [])

  private
    fresh : Term → ParseTerm M Nat
    fresh t =
      get >>= uncurry′ λ i Γ →
      i <$ put (suc i , (t , i) ∷ Γ)

    pAtom : Term → ParseTerm M Nat
    pAtom v = maybe (fresh v) pure =<< gets (flip lookup v ∘ snd)

  module _ {F : Set → Set} {{_ : Functor F}} {{_ : Traversable F}} {E : Set}
           (mkVar : Nat → E) (matchTm : Term → Maybe (F Term)) (fold : F E → M E) where

    {-# TERMINATING #-}
    parseTerm : Term → ParseTerm M E
    parseTerm v =
      case matchTm v of λ
      { nothing  → mkVar <$> pAtom v
      ; (just s) → lift ∘ fold =<< traverse parseTerm s
      }
