
module Tactic.Monoid.Reflect where

open import Prelude
open import Tactic.Reflection
open import Tactic.Reflection.Match

open import Control.Monad.State
open import Data.Monoid

open import Tactic.Monoid.Exp

P : Set → Set
P = StateT (List (Term × Nat)) TC

runP : ∀ {A} → P A → TC (A × List Term)
runP p = second (reverse ∘ map fst) <$> runStateT p []

pAtom : Term → P Exp
pAtom v =
  do tbl ← get
  -| case lookup tbl v of λ
     { nothing →
         do n := length tbl
         -| put ((v , n) ∷ tbl)
         ~| pure (var n)
     ; (just n) → pure (var n) }

module _ (isZero : Term → Bool) (isPlus : Term → Maybe (Term × Term)) where

  {-# TERMINATING #-}
  parseTerm : Term → P Exp
  parseTerm v =
    case isPlus v of λ
    { (just (x , y)) → _⊕_ <$> parseTerm x <*> parseTerm y
    ; nothing        → if isZero v then pure ε else pAtom v
    }

  parseEqn : Term → P (Exp × Exp)
  parseEqn (def (quote _≡_) (_ ∷ _ ∷ vArg x ∷ vArg y ∷ [])) =
    _,_ <$> parseTerm x <*> parseTerm y
  parseEqn goal = lift $ typeError (strErr "Not an equality goal:" ∷ termErr goal ∷ [])

get<> : ∀ {a} {A : Set a} → Monoid A → TC Term
get<> {A = A} dict =
  do `A    ← quoteTC A
  -| `plus ← quoteTC (Monoid._<>_ dict)
  -| (extendContext (vArg `A) $
      extendContext (vArg $ weaken 1 `A) $
      normalise (safeApply (weaken 2 `plus) (vArg (safe (var 0 []) _) ∷ vArg (safe (var 1 []) _) ∷ [])))

match<> : ∀ {a} {A : Set a} → Monoid A → TC (Term → Maybe (Term × Term))
match<> dict =
  do pat ← get<> dict
  -| pure λ v → caseF match 2 pat v of λ
                 { (x ∷ y ∷ []) → x , y }

matchEmpty : ∀ {a} {A : Set a} → Monoid A → TC (Term → Bool)
matchEmpty dict =
  do v ← quoteTC (Monoid.mempty dict)
  -| pure (isYes ∘ (v ==_))

lookupEnv : ∀ {a} {A : Set a} {{_ : Monoid A}} → List A → Nat → A
lookupEnv xs i = maybe mempty id (index xs i)

quoteList : List Term → Term
quoteList = foldr (λ x xs → con₂ (quote List._∷_) x xs) (con₀ (quote List.[]))

quoteEnv : Term → List Term → Term
quoteEnv dict xs = def (quote lookupEnv) (iArg dict ∷ vArg (quoteList xs) ∷ [])
