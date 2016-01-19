
module Tactic.Nat.Reflect where

open import Prelude
open import Builtin.Reflection
open import Tactic.Reflection.Quote
open import Tactic.Reflection.DeBruijn
open import Control.Monad.State
open import Tactic.Reflection.Equality

open import Tactic.Nat.Exp

R = StateT (Nat × List (Term × Nat)) TC

fail : ∀ {A} → R A
fail = lift (typeErrorS "reflection error")

_catch_ : ∀ {A} → R A → R A → R A
m catch h = stateT (λ s → catchTC (runStateT h s) (runStateT m s))

liftMaybe : ∀ {A} → Maybe A → R A
liftMaybe = maybe fail pure

runR : ∀ {A} → R A → TC (Maybe (A × List Term))
runR r =
  catchTC (just ∘ second (reverse ∘ map fst ∘ snd) <$>
           runStateT r (0 , []))
          (return nothing)

pattern `Nat = def (quote Nat) []

infixr 1 _`->_
infix  4 _`≡_

pattern _`≡_ x y = def (quote _≡_) (_ ∷ hArg `Nat ∷ vArg x ∷ vArg y ∷ [])
pattern _`->_ a b = pi (vArg (el (lit 0) a)) (abs _ (el (lit 0) b))

pattern _`+_ x y = def (quote _+N_) (vArg x ∷ vArg y ∷ [])
pattern _`*_ x y = def (quote _*N_) (vArg x ∷ vArg y ∷ [])
pattern `0       = `zero
pattern `1       = `suc `0

fresh : Term → R (Exp Var)
fresh t =
  get >>= uncurry′ λ i Γ →
   var i <$ put (suc i , (t , i) ∷ Γ)

⟨suc⟩ : ∀ {X} → Exp X → Exp X
⟨suc⟩ (lit n) = lit (suc n)
⟨suc⟩ (lit n ⟨+⟩ e) = lit (suc n) ⟨+⟩ e
⟨suc⟩ e = lit 1 ⟨+⟩ e

termToExpR : Term → R (Exp Var)
termToExpR (a `+ b) = _⟨+⟩_ <$> termToExpR a <*> termToExpR b
termToExpR (a `* b) = _⟨*⟩_ <$> termToExpR a <*> termToExpR b
termToExpR `0       = pure (lit 0)
termToExpR (`suc a) = ⟨suc⟩ <$> termToExpR a
termToExpR (lit (nat n)) = pure (lit n)
termToExpR (meta x _) = lift (blockOnMeta x)
termToExpR unknown  = fail
termToExpR t =
  gets (flip lookup t ∘ snd) >>=
  λ { nothing  → fresh t
    ; (just i) → pure (var i) }

private
  lower : Nat → Term → R Term
  lower 0 = pure
  lower i = liftMaybe ∘ strengthen i

termToEqR : Term → R (Exp Var × Exp Var)
termToEqR (lhs `≡ rhs) = _,_ <$> termToExpR lhs <*> termToExpR rhs
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
defaultArg = arg (arg-info visible relevant)

data ProofError {a} : Set a → Set (lsuc a) where
  bad-goal : ∀ g → ProofError g

qProofError : Term → Term
qProofError v = con (quote bad-goal) (defaultArg v ∷ [])

implicitArg instanceArg : ∀ {A} → A → Arg A
implicitArg = arg (arg-info hidden relevant)
instanceArg = arg (arg-info instance′ relevant)

instance
  QuotableExp : {Atom : Set} {{_ : Quotable Atom}} → Quotable (Exp Atom)
  QuotableExp {Atom} = record { ` = quoteExp }
    where
      quoteExp : Exp Atom → Term
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
stripImplicit (meta x args) = meta x (stripImplicitArgs args)
stripImplicit (lam v t) = lam v (stripImplicitAbsTerm t)
stripImplicit (pi t₁ t₂) = pi (stripImplicitArgType t₁) (stripImplicitAbsType t₂)
stripImplicit (agda-sort x) = agda-sort x
stripImplicit (lit l) = lit l
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

