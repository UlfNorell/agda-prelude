
module Tactic.Nat.Reflect where

open import Prelude hiding (abs)
open import Prelude.Variables
open import Control.Monad.State
open import Control.Monad.Transformer

import Agda.Builtin.Nat as Builtin

open import Builtin.Reflection
open import Tactic.Reflection
open import Tactic.Reflection.Quote
open import Tactic.Reflection.Meta
open import Tactic.Deriving.Quotable
open import Tactic.Reflection.Equality

open import Tactic.Nat.Exp

R = StateT (Nat × List (Term × Nat)) TC

fail : R A
fail = lift (typeErrorS "reflection error")

liftMaybe : Maybe A → R A
liftMaybe = maybe fail pure

runR : R A → TC (Maybe (A × List Term))
runR r =
  maybeA (second (reverse ∘ map fst ∘ snd) <$> runStateT r (0 , []))

pattern `Nat = def (quote Nat) []

infixr 1 _`->_
infix  4 _`≡_

pattern _`≡_ x y = def (quote _≡_) (_ ∷ hArg `Nat ∷ vArg x ∷ vArg y ∷ [])
pattern _`->_ a b = pi (vArg a) (abs _ b)

pattern _`+_ x y = def₂ (quote Builtin._+_) x y
pattern _`*_ x y = def₂ (quote Builtin._*_) x y
pattern `0       = con₀ (quote Nat.zero)
pattern `suc n   = con₁ (quote Nat.suc) n

fresh : Term → R (Exp Var)
fresh t =
  get >>= uncurry′ λ i Γ →
   var i <$ put (suc i , (t , i) ∷ Γ)

⟨suc⟩ : Exp A → Exp A
⟨suc⟩ (lit n) = lit (suc n)
⟨suc⟩ (lit n ⟨+⟩ e) = lit (suc n) ⟨+⟩ e
⟨suc⟩ e = lit 1 ⟨+⟩ e

private
  forceInstance : Name → Term → R ⊤
  forceInstance i v = lift $ unify v (def₀ i)
  forceSemiring = forceInstance (quote SemiringNat)
  forceNumber   = forceInstance (quote NumberNat)

termToExpR : Term → R (Exp Var)
termToExpR (a `+ b) = ⦇ termToExpR a ⟨+⟩ termToExpR b ⦈
termToExpR (a `* b) = ⦇ termToExpR a ⟨*⟩ termToExpR b ⦈
termToExpR (def (quote Semiring._+_) (_ ∷ _ ∷ vArg i@(meta x _) ∷ vArg a ∷ vArg b ∷ [])) = do
  forceSemiring i
  ⦇ termToExpR a ⟨+⟩ termToExpR b ⦈
termToExpR (def (quote Semiring._*_) (_ ∷ _ ∷ vArg i@(meta x _) ∷ vArg a ∷ vArg b ∷ [])) = do
  lift $ unify i (def₀ (quote SemiringNat))
  ⦇ termToExpR a ⟨*⟩ termToExpR b ⦈
termToExpR (def (quote Semiring.zro) (_ ∷ _ ∷ vArg i@(meta x _) ∷ [])) = do
  forceSemiring i
  pure (lit 0)
termToExpR (def (quote Semiring.one) (_ ∷ _ ∷ vArg i@(meta x _) ∷ [])) = do
  forceSemiring i
  pure (lit 1)
termToExpR (def (quote Number.fromNat) (_ ∷ _ ∷ vArg i@(meta x _) ∷ vArg a ∷ _ ∷ [])) = do
  forceNumber i
  termToExpR a
termToExpR `0       = pure (lit 0)
termToExpR (`suc a) = ⟨suc⟩ <$> termToExpR a
termToExpR (lit (nat n)) = pure (lit n)
termToExpR (meta x _) = lift (blockOnMeta x)
termToExpR unknown  = fail
termToExpR t = do
  lift (ensureNoMetas t)
  just i ← gets (flip lookup t ∘ snd) where nothing → fresh t
  pure (var i)

private
  lower : Nat → Term → R Term
  lower 0 = pure
  lower i = liftMaybe ∘ strengthen i

termToEqR : Term → R (Exp Var × Exp Var)
termToEqR (lhs `≡ rhs) = ⦇ termToExpR lhs , termToExpR rhs ⦈
termToEqR (def (quote _≡_) (_ ∷ hArg (meta x _) ∷ _)) = lift (blockOnMeta x)
termToEqR (meta x _) = lift (blockOnMeta x)
termToEqR _ = fail

termToHypsR′ : Nat → Term → R (List (Exp Var × Exp Var))
termToHypsR′ i (hyp `-> a) = _∷_ <$> (termToEqR =<< lower i hyp) <*> termToHypsR′ (suc i) a
termToHypsR′ _ (meta x _) = lift (blockOnMeta x)
termToHypsR′ i a = [_] <$> (termToEqR =<< lower i a)

termToHypsR : Term → R (List (Exp Var × Exp Var))
termToHypsR = termToHypsR′ 0

termToHyps : Term → TC (Maybe (List (Exp Var × Exp Var) × List Term))
termToHyps t = runR (termToHypsR t)

termToEq : Term → TC (Maybe ((Exp Var × Exp Var) × List Term))
termToEq t = runR (termToEqR t)

buildEnv : List Nat → Env Var
buildEnv []        i      = 0
buildEnv (x ∷ xs)  zero   = x
buildEnv (x ∷ xs) (suc i) = buildEnv xs i

defaultArg : Term → Arg Term
defaultArg = arg (arg-info visible default-modality)

data ProofError {a} : Set a → Set (lsuc a) where
  bad-goal : ∀ g → ProofError g

qProofError : Term → Term
qProofError v = con (quote bad-goal) (defaultArg v ∷ [])

implicitArg instanceArg : A → Arg A
implicitArg = arg (arg-info hidden default-modality)
instanceArg = arg (arg-info instance′ default-modality)

unquoteDecl QuotableExp = deriveQuotable QuotableExp (quote Exp)

stripImplicitArg : Arg Term → List (Arg Term)
stripImplicitArgs : List (Arg Term) → List (Arg Term)
stripImplicitAbsTerm : Abs Term → Abs Term
stripImplicitArgTerm : Arg Term → Arg Term

stripImplicit : Term → Term
stripImplicit (var x args) = var x (stripImplicitArgs args)
stripImplicit (con c args) = con c (stripImplicitArgs args)
stripImplicit (def f args) = def f (stripImplicitArgs args)
stripImplicit (meta x args) = meta x (stripImplicitArgs args)
stripImplicit (lam v t) = lam v (stripImplicitAbsTerm t)
stripImplicit (pi t₁ t₂) = pi (stripImplicitArgTerm t₁) (stripImplicitAbsTerm t₂)
stripImplicit (agda-sort x) = agda-sort x
stripImplicit (lit l) = lit l
stripImplicit (pat-lam cs args) = pat-lam cs (stripImplicitArgs args)
stripImplicit unknown = unknown

stripImplicitAbsTerm (abs x v) = abs x (stripImplicit v)

stripImplicitArgs [] = []
stripImplicitArgs (a ∷ as) = stripImplicitArg a ++ stripImplicitArgs as

stripImplicitArgTerm (arg i x) = arg i (stripImplicit x)

stripImplicitArg (arg (arg-info visible r) x) = arg (arg-info visible r) (stripImplicit x) ∷ []
stripImplicitArg (arg (arg-info hidden r) x) = []
stripImplicitArg (arg (arg-info instance′ r) x) = []

quotedEnv : List Term → Term
quotedEnv ts = def (quote buildEnv) $ defaultArg (quoteList $ map stripImplicit ts) ∷ []

QED : ∀ {a} {A : Set a} {x : Maybe A} → Set
QED {x = x} = IsJust x

get-proof : ∀ {a} {A : Set a} (prf : Maybe A) → QED {x = prf} → A
get-proof (just eq) _ = eq
get-proof nothing ()
{-# STATIC get-proof #-}

getProof : Name → Term → Term → Term
getProof err t proof =
  def (quote get-proof)
  $ vArg proof
  ∷ vArg (def err $ vArg (stripImplicit t) ∷ [])
  ∷ []

failedProof : Name → Term → Term
failedProof err t =
  def (quote get-proof)
  $ vArg (con (quote nothing) [])
  ∷ vArg (def err $ vArg (stripImplicit t) ∷ [])
  ∷ []

cantProve : Set → ⊤
cantProve _ = _

invalidGoal : Set → ⊤
invalidGoal _ = _
