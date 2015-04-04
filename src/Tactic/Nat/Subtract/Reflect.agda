
module Tactic.Nat.Subtract.Reflect where

open import Prelude
open import Builtin.Reflection
open import Control.Monad.State
open import  Tactic.Reflection.Quote

open import Tactic.Nat.Reflect
open import Tactic.Nat.Subtract.Exp

⟨suc⟩s : SubExp → SubExp
⟨suc⟩s (lit n) = lit (suc n)
⟨suc⟩s (lit n ⟨+⟩ e) = lit (suc n) ⟨+⟩ e
⟨suc⟩s e = lit 1 ⟨+⟩ e

freshS : Term → R SubExp
freshS t =
  get >>= uncurry′ λ i Γ →
  var i <$ put (suc i , (t , i) ∷ Γ)

pattern _`-_ x y = def (quote _-_) (vArg x ∷ vArg y ∷ [])

termToSubExpR : Term → R SubExp
termToSubExpR (a `+ b) = _⟨+⟩_ <$> termToSubExpR a <*> termToSubExpR b
termToSubExpR (a `* b) = _⟨*⟩_ <$> termToSubExpR a <*> termToSubExpR b
termToSubExpR (a `- b) = _⟨-⟩_ <$> termToSubExpR a <*> termToSubExpR b
termToSubExpR `0       = pure (lit 0)
termToSubExpR (`suc a) = ⟨suc⟩s <$> termToSubExpR a
termToSubExpR (lit (nat n)) = pure (lit n)
termToSubExpR unknown  = fail
termToSubExpR t =
  gets (flip lookup t ∘ snd) >>=
  λ { nothing  → freshS t
    ; (just i) → pure (var i) }

termToSubEqR : Term → R (SubExp × SubExp)
termToSubEqR (lhs `≡ rhs) = _,_ <$> termToSubExpR lhs <*> termToSubExpR rhs
termToSubEqR _ = fail

termToSubEq : Term → Maybe ((SubExp × SubExp) × List Term)
termToSubEq t = runR (termToSubEqR t)

instance
  QuotableSubExp : Quotable SubExp
  QuotableSubExp = record { ` = quoteSubExp }
    where
      quoteSubExp : SubExp → Term
      quoteSubExp (var x) = con (quote SubExp.var) (vArg (` x) ∷ [])
      quoteSubExp (lit n) = con (quote SubExp.lit) (vArg (` n) ∷ [])
      quoteSubExp (e ⟨+⟩ e₁) = con (quote SubExp._⟨+⟩_) (map defaultArg $ quoteSubExp e ∷ quoteSubExp e₁ ∷ [])
      quoteSubExp (e ⟨-⟩ e₁) = con (quote SubExp._⟨-⟩_) (map defaultArg $ quoteSubExp e ∷ quoteSubExp e₁ ∷ [])
      quoteSubExp (e ⟨*⟩ e₁) = con (quote SubExp._⟨*⟩_) (map defaultArg $ quoteSubExp e ∷ quoteSubExp e₁ ∷ [])
