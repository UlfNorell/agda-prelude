
module Tactic.Reflection.Substitute where

open import Prelude
open import Builtin.Reflection
open import Tactic.Reflection.DeBruijn

patternArgsVars : List (Arg Pattern) → Nat

patternVars : Pattern → Nat
patternVars (con _ ps) = patternArgsVars ps
patternVars dot = 1
patternVars (var _) = 1
patternVars (lit x) = 0
patternVars (proj _) = 0
patternVars absurd = 0

patternArgsVars [] = 0
patternArgsVars (arg _ p ∷ ps) = patternVars p + patternArgsVars ps

IsSafe : Term → Set
IsSafe (lam _ _) = ⊥
IsSafe _ = ⊤

data SafeTerm : Set where
  safe : (v : Term) (p : IsSafe v) → SafeTerm

maybeSafe : Term → Maybe SafeTerm
maybeSafe (var x args) = just (safe (var x args) _)
maybeSafe (con c args) = just (safe (con c args) _)
maybeSafe (def f args) = just (safe (def f args) _)
maybeSafe (meta x args) = just (safe (meta x args) _)
maybeSafe (lam v t) = nothing
maybeSafe (pat-lam cs args) = just (safe (pat-lam cs args) _)
maybeSafe (pi a b) = just (safe (pi a b) _)
maybeSafe (agda-sort s) = just (safe (agda-sort s) _)
maybeSafe (lit l) = just (safe (lit l) _)
maybeSafe unknown = just (safe unknown _)

instance
  DeBruijnSafeTerm : DeBruijn SafeTerm
  DeBruijnSafeTerm = record { strengthenFrom = str ; weakenFrom = wk }
    where
      -- Strengthening or weakening safe terms always results in safe terms,
      -- but proving that is a bit of a bother, thus maybeSafe.
      str : Nat → Nat → SafeTerm → Maybe SafeTerm
      str k n (safe v _) = v₁ ← strengthenFrom k n v
                        -| maybeSafe v₁

      wk : Nat → Nat → SafeTerm → SafeTerm
      wk k n (safe v p) = maybe (safe unknown _) id (maybeSafe (weakenFrom k n v))

safe-term : SafeTerm → Term
safe-term (safe v _) = v

applyTerm : SafeTerm → List (Arg Term) → Term
applyTerm v [] = safe-term v
applyTerm (safe (var x args) _) args₁ = var x (args ++ args₁)
applyTerm (safe (con c args) _) args₁ = con c (args ++ args₁)
applyTerm (safe (def f args) _) args₁ = def f (args ++ args₁)
applyTerm (safe (meta x args) _) args₁ = meta x (args ++ args₁)
applyTerm (safe (lam v t) ()) args
applyTerm (safe (pat-lam cs args) _) args₁ = pat-lam cs (args ++ args₁)
applyTerm (safe (pi a b) _) _ = pi a b
applyTerm (safe (agda-sort s) _) _ = agda-sort s
applyTerm (safe (lit l) _)  _ = lit l
applyTerm (safe unknown _) _ = unknown

Subst : Set → Set
Subst A = List SafeTerm → A → A

substTerm : Subst Term
substArgs : Subst (List (Arg Term))
substArg : Subst (Arg Term)
substAbs : Subst (Abs Term)
substSort : Subst Sort
substClauses : Subst (List Clause)
substClause : Subst Clause

substTerm σ (var x args) =
  case index σ x of λ
  { nothing  → var (x - length σ) (substArgs σ args)
  ; (just v) → applyTerm v (substArgs σ args) }
substTerm σ (con c args) = con c (substArgs σ args)
substTerm σ (def f args) = def f (substArgs σ args)
substTerm σ (meta x args) = meta x (substArgs σ args)
substTerm σ (lam v b) = lam v (substAbs σ b)
substTerm σ (pat-lam cs args) = pat-lam (substClauses σ cs) (substArgs σ args)
substTerm σ (pi a b) = pi (substArg σ a) (substAbs σ b)
substTerm σ (agda-sort s) = agda-sort (substSort σ s)
substTerm σ (lit l) = lit l
substTerm σ unknown = unknown

substSort σ (set t) = set (substTerm σ t)
substSort σ (lit n) = lit n
substSort σ unknown = unknown

substClauses σ [] = []
substClauses σ (c ∷ cs) = substClause σ c ∷ substClauses σ cs

substClause σ (clause ps b) =
  case patternArgsVars ps of λ
  { zero    → clause ps (substTerm σ b)
  ; (suc n) → clause ps (substTerm (reverse (map (λ i → safe (var i []) _) (from 0 to n)) ++ weaken (suc n) σ) b)
  }
substClause σ (absurd-clause ps) = absurd-clause ps

substArgs σ [] = []
substArgs σ (x ∷ args) = substArg σ x ∷ substArgs σ args
substArg σ (arg i x) = arg i (substTerm σ x)
substAbs σ (abs x v) = abs x $ substTerm (safe (var 0 []) _ ∷ weaken 1 σ) v

private
  toArgs : Nat → List (Arg SafeTerm) → List (Arg Term)
  toArgs k = map (weaken k ∘ fmap safe-term)

  SafeApplyType : Set → Set
  SafeApplyType A = List SafeTerm → Nat → A → List (Arg SafeTerm) → A

  safeApplyAbs : SafeApplyType (Abs Term)
  safeApplyArg : SafeApplyType (Arg Term)
  safeApplySort : SafeApplyType Sort

  -- safeApply′ env |Θ| v args = v′
  --   where Γ, Δ, Θ ⊢ v
  --         Γ ⊢ env : Δ
  --         Γ ⊢ args
  --         Γ, Θ ⊢ v′
  safeApply′ : List SafeTerm → Nat → Term → List (Arg SafeTerm) → Term
  safeApply′ env k (var x args) args₁ =
    if x <? k then var x (args ++ toArgs k args₁)
              else case index env (x - k) of λ
                   { nothing  → var (x - length env) (args ++ toArgs k args₁)
                   ; (just v) → applyTerm v (args ++ toArgs k args₁) }
  safeApply′ env k (con c args)      args₁      = con c (args ++ toArgs k args₁)
  safeApply′ env k (def f args)      args₁      = def f (args ++ toArgs k args₁)
  safeApply′ env k (lam v t)        (a ∷ args₁) = safeApply′ (unArg a ∷ env) k (unAbs t) args₁
  safeApply′ env k (lam v b)         []         = lam v $ safeApplyAbs env k b []
  safeApply′ env k (pat-lam cs args) args₁      = pat-lam cs (args ++ toArgs k args₁)
                                                  -- not right if applying to constructors
  safeApply′ env k (pi a b)          _          = pi (safeApplyArg env k a []) (safeApplyAbs env k b [])
  safeApply′ env k (agda-sort s)     args₁      = agda-sort (safeApplySort env k s [])
  safeApply′ env k (lit l)           args₁      = lit l
  safeApply′ env k (meta x args)     args₁      = meta x (args ++ toArgs k args₁)
  safeApply′ env k unknown           args₁      = unknown

  safeApplyAbs env k (abs x b) _ = abs x (safeApply′ env (suc k) b [])
  safeApplyArg env k (arg i v) args₁ = arg i (safeApply′ env k v args₁)

  safeApplySort env k (set t) _ = set (safeApply′ env k t [])
  safeApplySort env k (lit n) _ = lit n
  safeApplySort env k unknown _ = unknown

safeApply : Term → List (Arg SafeTerm) → Term
safeApply v args = safeApply′ [] 0 v args
