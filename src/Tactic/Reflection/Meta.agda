
module Tactic.Reflection.Meta where

open import Prelude
open import Builtin.Reflection
open import Tactic.Reflection.DeBruijn

ensureNoMetas : Term → TC ⊤

noMetaArg : Arg Term → TC ⊤
noMetaArg (arg _ v) = ensureNoMetas v

noMetaArgs : List (Arg Term) → TC ⊤
noMetaArgs [] = pure _
noMetaArgs (v ∷ vs) = noMetaArg v *> noMetaArgs vs

noMetaClause : Clause → TC ⊤
noMetaClause (clause ps t) = ensureNoMetas t
noMetaClause (absurd-clause ps) = pure _

noMetaClauses : List Clause → TC ⊤
noMetaClauses [] = pure _
noMetaClauses (c ∷ cs) = noMetaClause c *> noMetaClauses cs

noMetaAbs : Abs Term → TC ⊤
noMetaAbs (abs _ v) = ensureNoMetas v

noMetaSort : Sort → TC ⊤
noMetaSort (set t) = ensureNoMetas t
noMetaSort (lit n) = pure _
noMetaSort unknown = pure _

ensureNoMetas (var x args) = noMetaArgs args
ensureNoMetas (con c args) = noMetaArgs args
ensureNoMetas (def f args) = noMetaArgs args
ensureNoMetas (lam v (abs _ t)) = ensureNoMetas t
ensureNoMetas (pat-lam cs args) = noMetaClauses cs *> noMetaArgs args
ensureNoMetas (pi a b) = noMetaArg a *> noMetaAbs b
ensureNoMetas (agda-sort s) = noMetaSort s
ensureNoMetas (lit l) = pure _
ensureNoMetas (meta x x₁) = blockOnMeta x
ensureNoMetas unknown = pure _

normaliseNoMetas : Term → TC Term
normaliseNoMetas a = do a ← normalise a
                        stripBoundNames a <$ ensureNoMetas a
