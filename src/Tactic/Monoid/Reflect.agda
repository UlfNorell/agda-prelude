
module Tactic.Monoid.Reflect where

open import Prelude
open import Tactic.Reflection
open import Tactic.Reflection.Match

open import Control.Monad.State
open import Container.Traversable

open import Tactic.Monoid.Exp
open import Tactic.Reflection.Parse

private
  data ExpF (A : Set) : Set where
    eZero : ExpF A
    ePlus : A → A → ExpF A

  instance
    FunctorExpF : Functor ExpF
    fmap {{FunctorExpF}} _ eZero = eZero
    fmap {{FunctorExpF}} f (ePlus x y) = ePlus (f x) (f y)

    TraversableExpF : Traversable ExpF
    traverse {{TraversableExpF}} f eZero       = pure eZero
    traverse {{TraversableExpF}} f (ePlus x y) = pure ePlus <*> f x <*> f y

  mkExp : ExpF Exp → Exp
  mkExp eZero       = ε
  mkExp (ePlus x y) = x ⊕ y

module _ (match : Term → Maybe (ExpF Term)) where
  parseExp : Term → ParseTerm TC Exp
  parseExp v = parseTerm var match (pure ∘ mkExp) v

  parseEqn : Term → ParseTerm TC (Exp × Exp)
  parseEqn (def (quote _≡_) (_ ∷ _ ∷ vArg x ∷ vArg y ∷ [])) =
    _,_ <$> parseExp x <*> parseExp y
  parseEqn goal = lift $ typeError (strErr "Not an equality goal:" ∷ termErr goal ∷ [])

  parseGoal : Term → TC ((Exp × Exp) × List Term)
  parseGoal v = runParse (parseEqn v)

private
  match<> : ∀ {a} {A : Set a} → Monoid A → TC (Term → Maybe (Vec Term 2))
  match<> {A = A} dict =
    do `A    ← quoteTC A
    -| `plus ← quoteTC (Monoid._<>_ dict)
    -| (extendContext (vArg `A) $
        extendContext (vArg $ weaken 1 `A) $
        match 2 <$> normalise (safeApply (weaken 2 `plus) (vArg (safe (var 0 []) _) ∷
                                                           vArg (safe (var 1 []) _) ∷ [])))

  matchEmpty : ∀ {a} {A : Set a} → Monoid A → TC (Term → Bool)
  matchEmpty dict =
    do v ← quoteTC (Monoid.mempty dict)
    -| pure (isYes ∘ (v ==_))

monoidMatcher : ∀ {a} {A : Set a} → Monoid A → TC (Term → Maybe (ExpF Term))
monoidMatcher dict =
  do isZ ← matchEmpty dict
  -| isP ← match<> dict
  -| pure λ v →
       guardA! (isZ v) (pure eZero) <|>
       (caseF isP v of λ
        { (x ∷ y ∷ []) → ePlus x y })

private
  lookupEnv : ∀ {a} {A : Set a} {{_ : Monoid A}} → List A → Nat → A
  lookupEnv xs i = maybe mempty id (index xs i)

  quoteList : List Term → Term
  quoteList = foldr (λ x xs → con₂ (quote List._∷_) x xs) (con₀ (quote List.[]))

quoteEnv : Term → List Term → Term
quoteEnv dict xs = def (quote lookupEnv) (iArg dict ∷ vArg (quoteList xs) ∷ [])
