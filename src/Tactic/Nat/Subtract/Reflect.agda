
module Tactic.Nat.Subtract.Reflect where

open import Prelude
import Agda.Builtin.Nat as Builtin
open import Builtin.Reflection
open import Control.Monad.State
open import Control.Monad.Transformer
open import Tactic.Reflection
open import Tactic.Reflection.Quote

open import Tactic.Nat.Reflect
open import Tactic.Nat.Subtract.Exp

⟨suc⟩s : SubExp →  SubExp
⟨suc⟩s (lit n) = lit (suc n)
⟨suc⟩s (lit n ⟨+⟩ e) = lit (suc n) ⟨+⟩ e
⟨suc⟩s e = lit 1 ⟨+⟩ e

freshS : Term → R SubExp
freshS t =
  get >>= uncurry′ λ i Γ →
  var i <$ put (suc i , (t , i) ∷ Γ)

pattern _`-_ x y = def (quote Builtin._-_) (vArg x ∷ vArg y ∷ [])

private
  forceInstance : Name → Term → R ⊤
  forceInstance i v = lift $ unify v (def₀ i)
  forceNumber   = forceInstance (quote NumberNat)
  forceSemiring = forceInstance (quote SemiringNat)
  forceSubtractive = forceInstance (quote SubtractiveNat)

termToSubExpR : Term → R SubExp
termToSubExpR (a `+ b) = _⟨+⟩_ <$> termToSubExpR a <*> termToSubExpR b
termToSubExpR (a `* b) = _⟨*⟩_ <$> termToSubExpR a <*> termToSubExpR b
termToSubExpR (a `- b) = _⟨-⟩_ <$> termToSubExpR a <*> termToSubExpR b
-- Handle unsolved instances
termToSubExpR (def (quote Semiring._+_) (_ ∷ _ ∷ vArg i@(meta _ _) ∷ vArg a ∷ vArg b ∷ [])) = do
  forceSemiring i
  ⦇ termToSubExpR a ⟨+⟩ termToSubExpR b ⦈
termToSubExpR (def (quote Semiring._*_) (_ ∷ _ ∷ vArg i@(meta _ _) ∷ vArg a ∷ vArg b ∷ [])) = do
  lift $ unify i (def₀ (quote SemiringNat))
  ⦇ termToSubExpR a ⟨*⟩ termToSubExpR b ⦈
termToSubExpR (def (quote Subtractive._-_) (_ ∷ _ ∷ vArg i@(meta _ _) ∷ vArg a ∷ vArg b ∷ [])) = do
  forceSubtractive i
  ⦇ termToSubExpR a ⟨-⟩ termToSubExpR b ⦈
termToSubExpR (def (quote Semiring.zro) (_ ∷ _ ∷ vArg i@(meta _ _) ∷ [])) = do
  forceSemiring i
  pure (lit 0)
termToSubExpR (def (quote Semiring.one) (_ ∷ _ ∷ vArg i@(meta _ _) ∷ [])) = do
  forceSemiring i
  pure (lit 1)
termToSubExpR (def (quote Number.fromNat) (_ ∷ _ ∷ vArg i@(meta _ _) ∷ vArg a ∷ _ ∷ [])) = do
  forceNumber i
  termToSubExpR a
termToSubExpR `0       = pure (lit 0)
termToSubExpR (`suc a) = ⟨suc⟩s <$> termToSubExpR a
termToSubExpR (meta x _) = lift (blockOnMeta x)
termToSubExpR (lit (nat n)) = pure (lit n)
termToSubExpR unknown  = fail
termToSubExpR t = do
  lift $ ensureNoMetas t
  just i ← gets (flip lookup t ∘ snd)
    where nothing → freshS t
  pure (var i)

termToSubEqR : Term → R (SubExp × SubExp)
termToSubEqR (lhs `≡ rhs) = _,_ <$> termToSubExpR lhs <*> termToSubExpR rhs
termToSubEqR (def (quote _≡_) (_ ∷ hArg (meta x _) ∷ _)) = lift (blockOnMeta x)
termToSubEqR _ = fail

termToSubEq : Term → TC (Maybe ((SubExp × SubExp) × List Term))
termToSubEq t = runR (termToSubEqR t)

pattern _`<_ a b = def (quote LessNat) (vArg a ∷ vArg b ∷ [])

termToSubEqnR : Term → R Eqn
termToSubEqnR (def (quote Ord._<_) (_ ∷ _ ∷ vArg i@(meta _ _) ∷ vArg lhs ∷ vArg rhs ∷ [])) = do
  forceInstance (quote OrdNat) i
  ⦇ termToSubExpR lhs :< termToSubExpR rhs ⦈
termToSubEqnR (lhs `< rhs) = _:<_ <$> termToSubExpR lhs <*> termToSubExpR rhs
termToSubEqnR (lhs `≡ rhs) = _:≡_ <$> termToSubExpR lhs <*> termToSubExpR rhs
termToSubEqnR (def (quote _≡_) (_ ∷ hArg (meta x _) ∷ _)) = lift (blockOnMeta x)
termToSubEqnR t = lift (ensureNoMetas t) *> fail

termToSubEqn : Term → TC (Maybe (Eqn × List Term))
termToSubEqn t = runR (termToSubEqnR t)

private
  lower : Nat → Term → R Term
  lower 0 = pure
  lower i = liftMaybe ∘ strengthen i

termToSubHypsR′ : Nat → Term → R (List Eqn)
termToSubHypsR′ i (pi (vArg hyp) (abs _ a)) =
  _∷_ <$> (termToSubEqnR =<< lower i hyp) <*> termToSubHypsR′ (suc i) a
termToSubHypsR′ _ (meta x _) = lift (blockOnMeta x)
termToSubHypsR′ i a = [_] <$> (termToSubEqnR =<< lower i a)

termToSubHypsR : Term → R (List Eqn)
termToSubHypsR = termToSubHypsR′ 0

termToSubHyps : Term → TC (Maybe (List Eqn × List Term))
termToSubHyps t = runR (termToSubHypsR t)

instance
  QuotableSubExp : Quotable SubExp
  ` {{QuotableSubExp}} (var x) = con (quote SubExp.var) (vArg (` x) ∷ [])
  ` {{QuotableSubExp}} (lit n) = con (quote SubExp.lit) (vArg (` n) ∷ [])
  ` {{QuotableSubExp}} (e ⟨+⟩ e₁) = con (quote SubExp._⟨+⟩_) (map defaultArg $ ` e ∷ ` e₁ ∷ [])
  ` {{QuotableSubExp}} (e ⟨-⟩ e₁) = con (quote SubExp._⟨-⟩_) (map defaultArg $ ` e ∷ ` e₁ ∷ [])
  ` {{QuotableSubExp}} (e ⟨*⟩ e₁) = con (quote SubExp._⟨*⟩_) (map defaultArg $ ` e ∷ ` e₁ ∷ [])

  QuotableEqn : Quotable Eqn
  ` {{QuotableEqn}} (a :≡ b) = con (quote _:≡_) (vArg (` a) ∷ vArg (` b) ∷ [])
  ` {{QuotableEqn}} (a :< b) = con (quote _:<_) (vArg (` a) ∷ vArg (` b) ∷ [])
