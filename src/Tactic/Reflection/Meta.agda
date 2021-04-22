
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

noMetaTel : List (String × Arg Type) → TC ⊤
noMetaTel [] = pure _
noMetaTel ((x , arg _ a) ∷ tel) = ensureNoMetas a *> noMetaTel tel

noMetaClause : Clause → TC ⊤
noMetaClause (clause tel ps t) = noMetaTel tel *> ensureNoMetas t
noMetaClause (absurd-clause tel ps) = pure _

noMetaClauses : List Clause → TC ⊤
noMetaClauses [] = pure _
noMetaClauses (c ∷ cs) = noMetaClause c *> noMetaClauses cs

noMetaAbs : Abs Term → TC ⊤
noMetaAbs (abs _ v) = ensureNoMetas v

noMetaSort : Sort → TC ⊤
noMetaSort (set t)     = ensureNoMetas t
noMetaSort (lit n)     = pure _
noMetaSort (prop t)    = ensureNoMetas t
noMetaSort (propLit n) = pure _
noMetaSort (inf n)     = pure _
noMetaSort unknown     = pure _

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
