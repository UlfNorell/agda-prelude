
module Tactic.Nat.Subtract.Reflect where

open import Prelude
open import Builtin.Reflection
open import Control.Monad.State
open import Tactic.Reflection.Quote
open import Tactic.Reflection.DeBruijn

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

pattern _`-_ x y = def (quote _-N_) (vArg x ∷ vArg y ∷ [])

termToSubExpR : Term → R SubExp
termToSubExpR (a `+ b) = _⟨+⟩_ <$> termToSubExpR a <*> termToSubExpR b
termToSubExpR (a `* b) = _⟨*⟩_ <$> termToSubExpR a <*> termToSubExpR b
termToSubExpR (a `- b) = _⟨-⟩_ <$> termToSubExpR a <*> termToSubExpR b
termToSubExpR `0       = pure (lit 0)
termToSubExpR (`suc a) = ⟨suc⟩s <$> termToSubExpR a
termToSubExpR (meta x _) = lift (blockOnMeta x)
termToSubExpR (lit (nat n)) = pure (lit n)
termToSubExpR unknown  = fail
termToSubExpR t =
  gets (flip lookup t ∘ snd) >>=
  λ { nothing  → freshS t
    ; (just i) → pure (var i) }

termToSubEqR : Term → R (SubExp × SubExp)
termToSubEqR (lhs `≡ rhs) = _,_ <$> termToSubExpR lhs <*> termToSubExpR rhs
termToSubEqR (def (quote _≡_) (_ ∷ hArg (meta x _) ∷ _)) = lift (blockOnMeta x)
termToSubEqR _ = fail

termToSubEq : Term → TC (Maybe ((SubExp × SubExp) × List Term))
termToSubEq t = runR (termToSubEqR t)

pattern _`<_ a b = def (quote LessNat) (vArg a ∷ vArg b ∷ [])

termToSubEqnR : Term → R Eqn
termToSubEqnR (lhs `< rhs) = _:<_ <$> termToSubExpR lhs <*> termToSubExpR rhs
termToSubEqnR (lhs `≡ rhs) = _:≡_ <$> termToSubExpR lhs <*> termToSubExpR rhs
termToSubEqnR (def (quote _≡_) (_ ∷ hArg (meta x _) ∷ _)) = lift (blockOnMeta x)
termToSubEqnR (meta x _) = lift (blockOnMeta x)
termToSubEqnR _ = fail

termToSubEqn : Term → TC (Maybe (Eqn × List Term))
termToSubEqn t = runR (termToSubEqnR t)

private
  lower : Nat → Term → R Term
  lower 0 = pure
  lower i = liftMaybe ∘ strengthen i

termToSubHypsR′ : Nat → Term → R (List Eqn)
termToSubHypsR′ i (pi (vArg (el _ hyp)) (abs _ (el _ a))) =
  _∷_ <$> (termToSubEqnR =<< lower i hyp) <*> termToSubHypsR′ (suc i) a
termToSubHypsR′ _ (meta x _) = lift (blockOnMeta x)
termToSubHypsR′ i a = [_] <$> (termToSubEqnR =<< lower i a)

termToSubHypsR : Term → R (List Eqn)
termToSubHypsR = termToSubHypsR′ 0

termToSubHyps : Term → TC (Maybe (List Eqn × List Term))
termToSubHyps t = runR (termToSubHypsR t)

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

  QuotableEqn : Quotable Eqn
  QuotableEqn = record { ` = quoteEqn }
    where
      quoteEqn : Eqn → Term
      quoteEqn (a :≡ b) = con (quote _:≡_) (vArg (` a) ∷ vArg (` b) ∷ [])
      quoteEqn (a :< b) = con (quote _:<_) (vArg (` a) ∷ vArg (` b) ∷ [])
