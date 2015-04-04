
module Tactic.Nat.Reflect where

open import Prelude
open import Builtin.Reflection
open import Tactic.Reflection.Quote
open import Tactic.Reflection.DeBruijn
open import Control.Monad.State
open import Tactic.Reflection.Equality

open import Tactic.Nat.Exp

R = StateT (Nat × List (Term × Nat)) Maybe

fail : ∀ {A} → R A
fail = lift nothing

_catch_ : ∀ {A} → R A → R A → R A
m catch h = stateT (λ s → maybe (runStateT h s) just (runStateT m s))

runR : ∀ {A} → R A → Maybe (A × List Term)
runR r =
  second (reverse ∘ map fst ∘ snd) <$>
  runStateT r (0 , [])

pattern `Nat = def (quote Nat) []

infixr 1 _`->_
infix  4 _`≡_

pattern _`≡_ x y = def (quote _≡_) (_ ∷ hArg `Nat ∷ vArg x ∷ vArg y ∷ [])
pattern _`->_ a b = pi (vArg (el (lit 0) a)) (abs _ (el (lit 0) b))

pattern _`+_ x y = def (quote _+_) (vArg x ∷ vArg y ∷ [])
pattern _`*_ x y = def (quote _*_) (vArg x ∷ vArg y ∷ [])
pattern `0       = `zero
pattern `1       = `suc `0

fresh : Term → R Exp
fresh t =
  get >>= uncurry′ λ i Γ →
   var i <$ put (suc i , (t , i) ∷ Γ)

⟨suc⟩ : Exp → Exp
⟨suc⟩ (lit n) = lit (suc n)
⟨suc⟩ (lit n ⟨+⟩ e) = lit (suc n) ⟨+⟩ e
⟨suc⟩ e = lit 1 ⟨+⟩ e

termToExpR : Term → R Exp
termToExpR (a `+ b) = _⟨+⟩_ <$> termToExpR a <*> termToExpR b
termToExpR (a `* b) = _⟨*⟩_ <$> termToExpR a <*> termToExpR b
termToExpR `0       = pure (lit 0)
termToExpR (`suc a) = ⟨suc⟩ <$> termToExpR a
termToExpR (lit (nat n)) = pure (lit n)
termToExpR unknown  = fail
termToExpR t =
  gets (flip lookup t ∘ snd) >>=
  λ { nothing  → fresh t
    ; (just i) → pure (var i) }

private
  lower : Nat → Term → R Term
  lower 0 = pure
  lower i = lift ∘ strengthen i

termToEqR : Term → R (Exp × Exp)
termToEqR (lhs `≡ rhs) = _,_ <$> termToExpR lhs <*> termToExpR rhs
termToEqR _ = fail

termToHypsR′ : Nat → Term → R (List (Exp × Exp))
termToHypsR′ i (hyp `-> a) = _∷_ <$> (termToEqR =<< lower i hyp) <*> termToHypsR′ (suc i) a
termToHypsR′ i a = [_] <$> (termToEqR =<< lower i a)

termToHypsR : Term → R (List (Exp × Exp))
termToHypsR = termToHypsR′ 0

termToHyps : Term → Maybe (List (Exp × Exp) × List Term)
termToHyps t = runR (termToHypsR t)

termToEq : Term → Maybe ((Exp × Exp) × List Term)
termToEq t = runR (termToEqR t)

buildEnv : List Nat → Env
buildEnv []        i      = 0
buildEnv (x ∷ xs)  zero   = x
buildEnv (x ∷ xs) (suc i) = buildEnv xs i

defaultArg : Term → Arg Term
defaultArg = arg (arg-info visible relevant)

data ProofError {a} : Set a → Set (lsuc a) where
  bad-goal : ∀ g → ProofError g

qProofError : Term → Term
qProofError v = con (quote bad-goal) (defaultArg v ∷ [])

implicitArg instanceArg : ∀ {A} → A → Arg A
implicitArg = arg (arg-info hidden relevant)
instanceArg = arg (arg-info instance′ relevant)

instance
  QuotableExp : Quotable Exp
  QuotableExp = record { ` = quoteExp }
    where
      quoteExp : Exp → Term
      quoteExp (var x) = con (quote Exp.var) (vArg (` x) ∷ [])
      quoteExp (lit n) = con (quote Exp.lit) (vArg (` n) ∷ [])
      quoteExp (e ⟨+⟩ e₁) = con (quote _⟨+⟩_) (map defaultArg $ quoteExp e ∷ quoteExp e₁ ∷ [])
      quoteExp (e ⟨*⟩ e₁) = con (quote _⟨*⟩_) (map defaultArg $ quoteExp e ∷ quoteExp e₁ ∷ [])

stripImplicitArg : Arg Term → List (Arg Term)
stripImplicitArgs : List (Arg Term) → List (Arg Term)
stripImplicitArgType : Arg Type → Arg Type
stripImplicitType : Type → Type
stripImplicitAbsTerm : Abs Term → Abs Term
stripImplicitAbsType : Abs Type → Abs Type

stripImplicit : Term → Term
stripImplicit (var x args) = var x (stripImplicitArgs args)
stripImplicit (con c args) = con c (stripImplicitArgs args)
stripImplicit (def f args) = def f (stripImplicitArgs args)
stripImplicit (lam v t) = lam v (stripImplicitAbsTerm t)
stripImplicit (pi t₁ t₂) = pi (stripImplicitArgType t₁) (stripImplicitAbsType t₂)
stripImplicit (sort x) = sort x
stripImplicit (lit l) = lit l
stripImplicit (quote-goal t) = quote-goal (stripImplicitAbsTerm t)
stripImplicit (quote-term t) = quote-term (stripImplicit t)
stripImplicit quote-context  = quote-context
stripImplicit (unquote-term t args) = unquote-term (stripImplicit t) (stripImplicitArgs args)
stripImplicit (pat-lam cs args) = pat-lam cs (stripImplicitArgs args)
stripImplicit unknown = unknown

stripImplicitType (el s v) = el s (stripImplicit v)
stripImplicitArgType (arg i a) = arg i (stripImplicitType a)
stripImplicitAbsTerm (abs x v) = abs x (stripImplicit v)
stripImplicitAbsType (abs x a) = abs x (stripImplicitType a)

stripImplicitArgs [] = []
stripImplicitArgs (a ∷ as) = stripImplicitArg a ++ stripImplicitArgs as

stripImplicitArg (arg (arg-info visible r) x) = arg (arg-info visible r) (stripImplicit x) ∷ []
stripImplicitArg (arg (arg-info hidden r) x) = []
stripImplicitArg (arg (arg-info instance′ r) x) = []

quoteList : List Term → Term
quoteList []       = con (quote List.[]) []
quoteList (t ∷ ts) = con (quote List._∷_) (defaultArg t ∷ defaultArg (quoteList ts) ∷ [])

quotedEnv : List Term → Term
quotedEnv ts = def (quote buildEnv) $ defaultArg (quoteList $ map stripImplicit ts) ∷ []

QED : {A : Set} {x : Maybe A} → Set
QED {x = x} = IsJust x

getProof : {A : Set} (prf : Maybe A) → QED {x = prf} → A
getProof (just eq) _ = eq
getProof nothing ()

failedProof : Name → Term → Term
failedProof err t =
  def (quote getProof)
  $ vArg (con (quote nothing) [])
  ∷ vArg (def err $ vArg (stripImplicit t) ∷ [])
  ∷ []

cantProve : Set → ⊤
cantProve _ = _

invalidGoal : Set → ⊤
invalidGoal _ = _

