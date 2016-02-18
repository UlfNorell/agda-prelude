-- Term matching.
module Tactic.Reflection.Match where

open import Prelude
open import Builtin.Reflection
open import Tactic.Reflection.Equality

open import Control.Monad.Zero
open import Control.Monad.State
open import Container.Traversable

private
  M : Nat → Set → Set
  M n = StateT (Vec (Maybe Term) n) Maybe

  fN : ∀ {n} (i : Nat) → IsTrue (lessNat i n) → Fin n
  fN i lt = fromNat i {{lt}}

  patVar : ∀ {n} → Nat → Nat → Maybe (Fin n)
  patVar {n} zero i with lessNat i n | fN {n} i
  ... | true  | toFin = just (toFin true)
  ... | false | _     = nothing
  patVar (suc k) zero    = nothing
  patVar (suc k) (suc i) = patVar k i

  upd : ∀ {a} {A : Set a} {n} → Fin n → A → Vec A n → Vec A n
  upd  zero   x (_ ∷ xs) = x ∷ xs
  upd (suc i) x (y ∷ xs) = y ∷ upd i x xs

  matchVar : ∀ {n} → Fin n → Term → M n ⊤
  matchVar i v =
    caseM flip indexVec i <$> get of λ
    { (just u) → guard (u == v) (pure _)
    ; nothing  → _ <$ modify (upd i (just v)) }

  MatchFun : Set → Set
  MatchFun A = ∀ {n} → Nat → A → A → M n ⊤

  matchTerm matchTerm′ : MatchFun Term
  matchArgs : MatchFun (List (Arg Term))
  matchArg : MatchFun (Arg Term)
  matchAbs : MatchFun (Abs Term)

  matchTerm k (var i []) v with patVar k i
  ... | just x  = matchVar x v
  ... | nothing = matchTerm′ k (var i []) v
  matchTerm k p v = matchTerm′ k p v

  matchTerm′ {n} k (var i args) (var j args₁) =
    guard! (j <? k && isYes (i == j) || j ≥? k && isYes (j + n == i))
           (matchArgs k args args₁)
  matchTerm′ k (con c args) (con c₁ args₁) = guard (c == c₁) (matchArgs k args args₁)
  matchTerm′ k (def f args) (def g args₁) = guard (f == g) (matchArgs k args args₁)
  matchTerm′ k (lam h p) (lam h₁ v) = guard (h == h₁) (matchAbs k p v)
  matchTerm′ k (pat-lam cs args) v = mzero -- todo
  matchTerm′ k (pi a b) (pi a₁ b₁) = matchArg k a a₁ >> matchAbs k b b₁
  matchTerm′ k (lit l) (lit l₁) = guard (l == l₁) (pure _)
  matchTerm′ k (agda-sort _) _ = pure _ -- ignore sorts
  matchTerm′ k (meta _ _) _ = pure _
  matchTerm′ k unknown _ = pure _
  matchTerm′ k p v = mzero

  matchArgs k (x ∷ xs) (y ∷ ys) = matchArg k x y >> matchArgs k xs ys
  matchArgs k [] [] = pure _
  matchArgs k _ _   = mzero

  matchAbs k (abs _ x) (abs _ y) = matchTerm (suc k) x y
  matchArg k (arg i x) (arg j y) = guard (i == j) (matchTerm k x y)

-- match |Δ| p v = just σ
--  where Γ, Δ ⊢ p
--        Γ    ⊢ v
--        Γ    ⊢ σ : Δ
--        p σ ≡ v
match : (n : Nat) → Term → Term → Maybe (Vec Term n)
match n pat v =
  do env ← snd <$> runStateT (matchTerm 0 pat v) (pure nothing ofType Vec (Maybe Term) n)
  -| traverse id env
