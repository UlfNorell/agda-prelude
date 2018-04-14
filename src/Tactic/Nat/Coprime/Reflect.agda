
module Tactic.Nat.Coprime.Reflect where

import Agda.Builtin.Nat as Builtin

open import Prelude
open import Control.Monad.State
open import Control.Monad.Zero
open import Container.Traversable
open import Numeric.Nat.GCD

open import Tactic.Reflection
open import Tactic.Reflection.Parse
open import Tactic.Reflection.Quote
open import Tactic.Deriving.Quotable
open import Tactic.Nat.Coprime.Problem

-- Reflection --

instance
  unquoteDecl QuoteExp     = deriveQuotable QuoteExp (quote Exp)
  unquoteDecl QuoteFormula = deriveQuotable QuoteFormula (quote Formula)
  unquoteDecl QuoteProblem = deriveQuotable QuoteProblem (quote Problem)

data ExpF (A : Set) : Set where
  atom : (x : Atom) → ExpF A
  _⊗_ : (a b : A) → ExpF A

instance
  FunExpF : Functor ExpF
  fmap ⦃ FunExpF ⦄ f (atom x) = atom x
  fmap ⦃ FunExpF ⦄ f (a ⊗ b) = f a ⊗ f b

  TravExpF : Traversable ExpF
  traverse ⦃ TravExpF ⦄ f (atom x) = pure (atom x)
  traverse ⦃ TravExpF ⦄ f (a ⊗ b) = ⦇ f a ⊗ f b ⦈

foldExp : ExpF Exp → Exp
foldExp (atom x) = atom x
foldExp (a ⊗ b) = a ⊗ b

-- Requires normalisation!
matchExp : Term → Maybe (ExpF Term)
matchExp (def₂ (quote Builtin._*_) a b) = just (a ⊗ b)
matchExp _ = nothing

parseExp : Term → ParseTerm TC Exp
parseExp = parseTerm atom matchExp foldExp

parseEq : Term → ParseTerm TC (Term × Term)
parseEq (def (quote _≡_) (_ ∷ _ ∷ vArg x ∷ vArg y ∷ [])) = pure (x , y)
parseEq (meta x _) = lift (blockOnMeta! x)
parseEq _ = empty

parseGCD : Term → ParseTerm TC (Term × Term)
parseGCD (def (quote get-gcd) (_ ∷ _ ∷ vArg (def₂ (quote gcd) a b) ∷ [])) = pure (a , b)
parseGCD (meta x _) = lift (blockOnMeta x)
parseGCD t = empty

parseFormula : Term → ParseTerm TC Formula
parseFormula t = do
  lhs , lit (nat 1) ← parseEq t where _ → empty
  a , b ← parseGCD lhs
  ⦇ parseExp a ⋈ parseExp b ⦈

underBinder : ParseTerm TC ⊤
underBinder = _ <$ modify (second $ map $ first $ weaken 1)

-- Parse a Problem from the context and goal type.
parseProblem : List Term → Term → ParseTerm TC (Nat × List Term × Problem)
parseProblem [] t = do
  φ ← parseFormula t
  pure (0 , [] , ([] ⊨ φ))
parseProblem (h ∷ Δ) t =
  caseM just <$> parseFormula h <|> pure nothing of λ where
    (just ψ) → do
      underBinder
      fv , Hs , (Γ ⊨ φ) ← parseProblem Δ t
      pure (suc fv , var fv [] ∷ Hs , (ψ ∷ Γ ⊨ φ))
    nothing  → do
      underBinder
      fv , Hs , Q ← parseProblem Δ t
      pure (suc fv , Hs , Q)

buildEnv : List Nat → Env
buildEnv []        i      = 0
buildEnv (x ∷ xs)  zero   = x
buildEnv (x ∷ xs) (suc i) = buildEnv xs i

quotedEnv : List Term → Term
quotedEnv ts = def₁ (quote buildEnv) (quoteList ts)
