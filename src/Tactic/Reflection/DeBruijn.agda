
module Tactic.Reflection.DeBruijn where

open import Prelude hiding (abs)
open import Builtin.Reflection
open import Container.Traversable

record DeBruijn {a} (A : Set a) : Set a where
  field
    strengthenFrom : (from n : Nat) → A → Maybe A
    weakenFrom     : (from n : Nat) → A → A

  strengthen : Nat → A → Maybe A
  strengthen 0 = just
  strengthen n = strengthenFrom 0 n

  weaken : Nat → A → A
  weaken zero = id
  weaken n    = weakenFrom 0 n

open DeBruijn {{...}} public

private
  Str : Set → Set
  Str A = Nat → Nat → A → Maybe A

  strVar : Str Nat
  strVar lo n x = if      x <? lo     then just x
                  else if x <? lo + n then nothing
                  else                just (x - n)

  strArgs    : Str (List (Arg Term))
  strArg     : Str (Arg Term)
  strSort    : Str Sort
  strClauses : Str (List Clause)
  strClause  : Str Clause
  strAbsTerm : Str (Abs Term)
  strAbsType : Str (Abs Type)

  strTerm : Str Term
  strTerm lo n (var x args)  = var <$> strVar lo n x <*> strArgs lo n args
  strTerm lo n (con c args)  = con c <$> strArgs lo n args
  strTerm lo n (def f args)  = def f <$> strArgs lo n args
  strTerm lo n (meta x args) = meta x <$> strArgs lo n args
  strTerm lo n (lam v t)     = lam v <$> strAbsTerm lo n t
  strTerm lo n (pi a b)      = pi    <$> strArg lo n a <*> strAbsType lo n b
  strTerm lo n (agda-sort s) = agda-sort <$> strSort lo n s
  strTerm lo n (lit l)       = just (lit l)
  strTerm lo n (pat-lam _ _) = just unknown -- todo
  strTerm lo n unknown       = just unknown

  strAbsTerm lo n (abs s t)  = abs s <$> strTerm (suc lo) n t
  strAbsType lo n (abs s t)  = abs s <$> strTerm (suc lo) n t

  strArgs    lo n []         = just []
  strArgs    lo n (x ∷ args) = _∷_   <$> strArg  lo n x <*> strArgs lo n args
  strArg     lo n (arg i v)  = arg i <$> strTerm lo n v
  strSort    lo n (set t)    = set   <$> strTerm lo n t
  strSort    lo n (lit l)    = just (lit l)
  strSort    lo n (prop t)   = prop <$> strTerm lo n t
  strSort    lo n (propLit t)= just (propLit t)
  strSort    lo n (inf l)    = just (inf l)
  strSort    lo n unknown    = just unknown

  strClauses lo k [] = just []
  strClauses lo k (c ∷ cs) = _∷_ <$> strClause lo k c <*> strClauses lo k cs

  strClause lo k (clause tel ps b)      = clause tel ps <$> strTerm (lo + length tel) k b
  strClause lo k (absurd-clause tel ps) = just (absurd-clause tel ps)

  strPat    : Str Pattern
  strPatArg : Str (Arg Pattern)
  strPats   : Str (List (Arg Pattern))

  strPat    lo k (con c ps) = con c <$> strPats lo k ps
  strPat    lo k (dot t)    = dot <$> strTerm lo k t
  strPat    lo k (var x)    = var <$> strVar lo k x
  strPat    lo k (lit l)    = pure (lit l)
  strPat    lo k (proj f)   = pure (proj f)
  strPat    lo k (absurd x) = absurd <$> strVar lo k x
  strPatArg lo k (arg i p)  = arg i <$> strPat lo k p
  strPats   lo k []         = pure []
  strPats   lo k (p ∷ ps)   = _∷_ <$> strPatArg lo k p <*> strPats lo k ps

private
  Wk : Set → Set
  Wk A = Nat → Nat → A → A

  wkVar : Wk Nat
  wkVar lo k x = if x <? lo then x else x + k

  wkArgs    : Wk (List (Arg Term))
  wkArg     : Wk (Arg Term)
  wkSort    : Wk Sort
  wkClauses : Wk (List Clause)
  wkClause  : Wk Clause
  wkAbsTerm : Wk (Abs Term)

  wk : Wk Term
  wk lo k (var x args)  = var (wkVar lo k x) (wkArgs lo k args)
  wk lo k (con c args)  = con c (wkArgs lo k args)
  wk lo k (def f args)  = def f (wkArgs lo k args)
  wk lo k (meta x args) = meta x (wkArgs lo k args)
  wk lo k (lam v t)     = lam v (wkAbsTerm lo k t)
  wk lo k (pi a b)      = pi (wkArg lo k a) (wkAbsTerm lo k b)
  wk lo k (agda-sort s) = agda-sort (wkSort lo k s)
  wk lo k (lit l)       = lit l
  wk lo k (pat-lam cs args) = pat-lam (wkClauses lo k cs) (wkArgs lo k args)
  wk lo k unknown       = unknown
  

  wkAbsTerm lo k (abs s t)   = abs s (wk (suc lo) k t)
  wkArgs    lo k []          = []
  wkArgs    lo k (x ∷ args)  = wkArg lo k x ∷ wkArgs lo k args
  wkArg     lo k (arg i v)   = arg i (wk lo k v)
  wkSort    lo k (set t)     = set (wk lo k t)
  wkSort    lo k (lit n)     = lit n
  wkSort    lo k (prop t)    = prop (wk lo k t)
  wkSort    lo k (propLit n) = propLit n
  wkSort    lo k (inf n)     = inf n
  wkSort    lo k unknown     = unknown

  wkClauses lo k [] = []
  wkClauses lo k (c ∷ cs) = wkClause lo k c ∷ wkClauses lo k cs

  wkClause lo k (clause tel ps b)      = clause tel ps (wk (lo + length tel) k b)
  wkClause lo k (absurd-clause tel ps) = absurd-clause tel ps

  wkPat    : Wk Pattern
  wkPatArg : Wk (Arg Pattern)
  wkPats   : Wk (List (Arg Pattern))

  wkPat    lo k (con c ps) = con c (wkPats lo k ps)
  wkPat    lo k (dot t)    = dot (wk lo k t)
  wkPat    lo k (var x)    = var (wkVar lo k x)
  wkPat    lo k (lit l)    = lit l
  wkPat    lo k (proj f)   = proj f
  wkPat    lo k (absurd x) = absurd (wkVar lo k x)
  wkPatArg lo k (arg i p)  = arg i (wkPat lo k p)
  wkPats   lo k []         = []
  wkPats   lo k (p ∷ ps)   = wkPatArg lo k p ∷ wkPats lo k ps

-- Instances --

DeBruijnTraversable : ∀ {a} {F : Set a → Set a} {{_ : Traversable F}}
                        {A : Set a} {{_ : DeBruijn A}} → DeBruijn (F A)
strengthenFrom {{DeBruijnTraversable}} lo k = traverse (strengthenFrom lo k)
weakenFrom     {{DeBruijnTraversable}} lo k = fmap     (weakenFrom lo k)

instance
  DeBruijnNat : DeBruijn Nat
  strengthenFrom {{DeBruijnNat}} = strVar
  weakenFrom     {{DeBruijnNat}} = wkVar

  DeBruijnTerm : DeBruijn Term
  strengthenFrom {{DeBruijnTerm}} = strTerm
  weakenFrom     {{DeBruijnTerm}} = wk

  DeBruijnPattern : DeBruijn Pattern
  strengthenFrom {{DeBruijnPattern}} = strPat
  weakenFrom     {{DeBruijnPattern}} = wkPat

  DeBruijnList : ∀ {a} {A : Set a} {{_ : DeBruijn A}} → DeBruijn (List A)
  DeBruijnList = DeBruijnTraversable

  DeBruijnVec : ∀ {a} {A : Set a} {{_ : DeBruijn A}} {n : Nat} → DeBruijn (Vec A n)
  DeBruijnVec = DeBruijnTraversable

  DeBruijnArg : {A : Set} {{_ : DeBruijn A}} → DeBruijn (Arg A)
  DeBruijnArg = DeBruijnTraversable

  DeBruijnMaybe : {A : Set} {{_ : DeBruijn A}} → DeBruijn (Maybe A)
  DeBruijnMaybe = DeBruijnTraversable

  DeBruijnPair : ∀ {a b} {A : Set a} {B : Set b} {{_ : DeBruijn A}} {{_ : DeBruijn B}} → DeBruijn (A × B)
  strengthenFrom {{DeBruijnPair}} lo k (x , y) = _,_ <$>′ strengthenFrom lo k x <*>′ strengthenFrom lo k y
  weakenFrom     {{DeBruijnPair}} lo k (x , y) = weakenFrom lo k x , weakenFrom lo k y

  DeBruijnString : DeBruijn String
  strengthenFrom {{DeBruijnString}} _ _ = just
  weakenFrom     {{DeBruijnString}} _ _ = id

-- Strip bound names (to ensure _==_ checks α-equality)
-- Doesn't touch pattern variables in pattern lambdas.

mutual

  stripBoundNames : Term → Term
  stripBoundNames (var x args)      = var x (stripArgs args)
  stripBoundNames (con c args)      = con c (stripArgs args)
  stripBoundNames (def f args)      = def f (stripArgs args)
  stripBoundNames (lam v t)         = lam v (stripAbs t)
  stripBoundNames (pat-lam cs args) = pat-lam (stripClauses cs) (stripArgs args)
  stripBoundNames (pi a b)          = pi (stripArg a) (stripAbs b)
  stripBoundNames (agda-sort s)     = agda-sort (stripSort s)
  stripBoundNames (lit l)           = lit l
  stripBoundNames (meta x args)     = meta x (stripArgs args)
  stripBoundNames unknown           = unknown

  private
    stripArgs : List (Arg Term) → List (Arg Term)
    stripArgs [] = []
    stripArgs (x ∷ xs) = stripArg x ∷ stripArgs xs

    stripArg : Arg Term → Arg Term
    stripArg (arg i t) = arg i (stripBoundNames t)

    stripAbs : Abs Term → Abs Term
    stripAbs (abs _ t) = abs "" (stripBoundNames t)

    stripClauses : List Clause → List Clause
    stripClauses [] = []
    stripClauses (x ∷ xs) = stripClause x ∷ stripClauses xs

    stripClause : Clause → Clause
    stripClause (clause tel ps t) = clause tel ps (stripBoundNames t)
    stripClause (absurd-clause tel ps) = absurd-clause tel ps

    stripSort : Sort → Sort
    stripSort (set t)     = set (stripBoundNames t)
    stripSort (lit n)     = lit n
    stripSort (prop t)    = prop (stripBoundNames t)
    stripSort (propLit n) = propLit n
    stripSort (inf n)     = inf n
    stripSort unknown     = unknown
