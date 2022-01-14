module Tactic.Monoid.Reflect where

open import Prelude
open import Tactic.Reflection
open import Tactic.Reflection.Match

open import Control.Monad.Zero
open import Control.Monad.State
open import Container.Traversable

open import Tactic.Monoid.Exp
open import Tactic.Reflection.Parse renaming (parseEqn to parseEq)

private
  data ExpF (A : Set) : Set where
    eVar  : Nat → ExpF A
    eZero : ExpF A
    ePlus : A → A → ExpF A

  instance
    FunctorExpF : Functor ExpF
    fmap {{FunctorExpF}} _ (eVar i) = eVar i
    fmap {{FunctorExpF}} _ eZero = eZero
    fmap {{FunctorExpF}} f (ePlus x y) = ePlus (f x) (f y)

    TraversableExpF : Traversable ExpF
    traverse {{TraversableExpF}} f (eVar i)    = pure (eVar i)
    traverse {{TraversableExpF}} f eZero       = pure eZero
    traverse {{TraversableExpF}} f (ePlus x y) = ⦇ ePlus (f x) (f y) ⦈

  mkExp : ExpF Exp → Exp
  mkExp (eVar i)    = var i
  mkExp eZero       = ε
  mkExp (ePlus x y) = x ⊕ y

module _ (match : Term → Maybe (ExpF Term)) where
  parseEqn : Term → ParseTerm TC (Exp × Exp)
  parseEqn v = parseEq eVar match mkExp v

  parseGoal : Term → TC ((Exp × Exp) × List Term)
  parseGoal v = runParse (parseEqn v)

private
  match<> : ∀ {a} {A : Set a} → Monoid A → TC (Term → Maybe (Vec Term 2))
  match<> {A = A} dict = do
    `A    ← quoteTC A
    `plus ← quoteTC (Semigroup._<>_ (Monoid.super dict))
    extendContext "x" (vArg `A) $
      extendContext "x" (vArg $ weaken 1 `A) $
      match 2 <$> normalise (safeApply (weaken 2 `plus) (vArg (safe (var 0 []) _) ∷
                                                         vArg (safe (var 1 []) _) ∷ []))

  matchEmpty : ∀ {a} {A : Set a} → Monoid A → TC (Term → Bool)
  matchEmpty dict = do
    v ← quoteTC (Monoid.mempty dict)
    pure (isYes ∘ (v ==_))

monoidMatcher : ∀ {a} {A : Set a} → Monoid A → TC (Term → Maybe (ExpF Term))
monoidMatcher dict = withNormalisation true $ do
  isZ ← matchEmpty dict
  isP ← match<> dict
  pure λ v →
       guard! (isZ v) (pure eZero) <|> do
         x ∷ y ∷ [] ←  isP v
         pure (ePlus x y)

private
  lookupEnv : ∀ {a} {A : Set a} {{_ : Monoid A}} → List A → Nat → A
  lookupEnv xs i = maybe mempty id (index xs i)

  quoteList : List Term → Term
  quoteList = foldr (λ x xs → con₂ (quote List._∷_) x xs) (con₀ (quote List.[]))

quoteEnv : Term → List Term → Term
quoteEnv dict xs = def (quote lookupEnv) (iArg dict ∷ vArg (quoteList xs) ∷ [])
