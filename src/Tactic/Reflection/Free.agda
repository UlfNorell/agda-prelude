
module Tactic.Reflection.Free where

open import Prelude
open import Builtin.Reflection
open import Tactic.Reflection.DeBruijn

VarSet = List Nat -- ordered

private
  _∪_ : VarSet → VarSet → VarSet
  []       ∪ ys = ys
  xs       ∪ [] = xs
  (x ∷ xs) ∪ (y ∷ ys) with compare x y
  ... | (less    _) = x ∷ (xs ∪ (y ∷ ys))
  ... | (equal   _) = x ∷ (xs ∪ ys)
  ... | (greater _) = y ∷ ((x ∷ xs) ∪ ys)

  ∅ : VarSet
  ∅ = []

record FreeVars {a} (A : Set a) : Set a where
  field freeVars : A → VarSet

open FreeVars {{...}} public

-- Instances --

private
  freeTerm : Nat → Term → VarSet
  freeType : Nat → Type → VarSet
  freeSort : Nat → Sort → VarSet
  freeArgTerm : Nat → Arg Term → VarSet
  freeArgType : Nat → Arg Type → VarSet
  freeArgs : Nat → List (Arg Term) → VarSet
  freeClauses : Nat → List Clause → VarSet
  freeClause : Nat → Clause → VarSet

  freeTerm n (var x args) =
    case compare (suc x) n of
    λ { (greater (diff k _)) → [ k ]
      ; _ → ∅
      }
  freeTerm n (con c args) = freeArgs n args
  freeTerm n (def f args) = freeArgs n args
  freeTerm n (lam _ (abs _ v)) = freeTerm (suc n) v
  freeTerm n (pat-lam cs args) = freeClauses n cs ∪ freeArgs n args
  freeTerm n (pi a (abs _ b))  = freeArgType n a ∪ freeType (suc n) b
  freeTerm n (sort s) = freeSort n s
  freeTerm n (lit l) = ∅
  freeTerm n unknown = ∅

  freeType n (el s t) = freeSort n s ∪ freeTerm n t
  freeSort n (set t) = freeTerm n t
  freeSort _ (lit n) = ∅
  freeSort _ unknown = ∅

  freeArgTerm n (arg i x) = freeTerm n x
  freeArgType n (arg i x) = freeType n x
  freeArgs n [] = ∅
  freeArgs n (a ∷ as) = freeArgTerm n a ∪ freeArgs n as

  freeClauses n [] = ∅
  freeClauses n (c ∷ cs) = freeClause n c ∪ freeClauses n cs

  freeClause n (clause ps b)     = freeTerm (patternBindings ps + n) b
  freeClause n (absurd-clause _) = ∅

instance
  FreeTerm : FreeVars Term
  FreeTerm = record { freeVars = freeTerm 0 }

  FreeType : FreeVars Type
  FreeType = record { freeVars = freeType 0 }

  FreeSort : FreeVars Sort
  FreeSort = record { freeVars = freeSort 0 }

  FreeArg : FreeVars (Arg Term)
  FreeArg = record { freeVars = freeArgTerm 0 }

  FreeArgs : FreeVars (List (Arg Term))
  FreeArgs = record { freeVars = freeArgs 0 }

  FreeArgType : FreeVars (Arg Type)
  FreeArgType = record { freeVars = freeArgType 0 }
