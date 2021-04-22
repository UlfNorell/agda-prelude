
module Tactic.Reflection.Free where

open import Prelude
open import Prelude.Variables
open import Builtin.Reflection
open import Tactic.Reflection.DeBruijn

VarSet = List Nat -- ordered

private
  _∪_ : VarSet → VarSet → VarSet
  []       ∪ ys = ys
  xs       ∪ [] = xs
  (x ∷ xs) ∪ (y ∷ ys) =
    case-cmp compare x y
      less    _ => x ∷ (xs ∪ (y ∷ ys))
      equal   _ => x ∷ (xs ∪ ys)
      greater _ => y ∷ ((x ∷ xs) ∪ ys)

  ∅ : VarSet
  ∅ = []

record FreeVars {a} (A : Set a) : Set a where
  field freeVars : A → VarSet

open FreeVars {{...}} public

-- Instances --

private
  freeTerm : Nat → Term → VarSet
  freeSort : Nat → Sort → VarSet
  freeArgTerm : Nat → Arg Term → VarSet
  freeArgs : Nat → List (Arg Term) → VarSet
  freeClauses : Nat → List Clause → VarSet
  freeClause : Nat → Clause → VarSet

  freeTerm n (var x args) = freeArgs n args ∪
    (case compare (suc x) n of
    λ { (greater (diff k _)) → [ k ]
      ; _ → ∅
      })
  freeTerm n (con c args) = freeArgs n args
  freeTerm n (def f args) = freeArgs n args
  freeTerm n (meta x args) = freeArgs n args
  freeTerm n (lam _ (abs _ v)) = freeTerm (suc n) v
  freeTerm n (pat-lam cs args) = freeClauses n cs ∪ freeArgs n args
  freeTerm n (pi a (abs _ b))  = freeArgTerm n a ∪ freeTerm (suc n) b
  freeTerm n (agda-sort s) = freeSort n s
  freeTerm n (lit l) = ∅
  freeTerm n unknown = ∅

  freeSort n (set t)     = freeTerm n t
  freeSort _ (lit n)     = ∅
  freeSort n (prop t)    = freeTerm n t
  freeSort _ (propLit n) = ∅
  freeSort _ (inf n)     = ∅
  freeSort _ unknown     = ∅

  freeArgTerm n (arg i x) = freeTerm n x
  freeArgs n [] = ∅
  freeArgs n (a ∷ as) = freeArgTerm n a ∪ freeArgs n as

  freeClauses n [] = ∅
  freeClauses n (c ∷ cs) = freeClause n c ∪ freeClauses n cs

  freeClause n (clause tel ps b)     = freeTerm (length tel + n) b
  freeClause n (absurd-clause tel _) = ∅

instance
  FreeTerm : FreeVars Term
  freeVars {{FreeTerm}} = freeTerm 0

  FreeSort : FreeVars Sort
  freeVars {{FreeSort}} = freeSort 0

  FreeArg : {{_ : FreeVars A}} → FreeVars (Arg A)
  freeVars {{FreeArg}} (arg _ x) = freeVars x

  FreeList : {{_ : FreeVars A}} → FreeVars (List A)
  freeVars {{FreeList}} = foldr (λ x → freeVars x ∪_) ∅
