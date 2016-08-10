
module Tactic.Reflection.DeBruijn where

open import Prelude
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

patternBindings : List (Arg Pattern) → Nat
patternBindings = binds
  where
    binds : List (Arg Pattern) → Nat
    bind  : Pattern → Nat

    binds []             = 0
    binds (arg _ a ∷ as) = bind a + binds as

    bind (con c ps) = binds ps
    bind dot        = 1
    bind (var _)    = 1
    bind (lit l)    = 0
    bind (proj x)   = 0
    bind absurd     = 0

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
  strSort    lo n unknown    = just unknown

  strClauses lo k [] = just []
  strClauses lo k (c ∷ cs) = _∷_ <$> strClause lo k c <*> strClauses lo k cs

  strClause lo k (clause ps b)      = clause ps <$> strTerm (lo + patternBindings ps) k b
  strClause lo k (absurd-clause ps) = just (absurd-clause ps)

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

  wkAbsTerm lo k (abs s t)  = abs s (wk (suc lo) k t)
  wkArgs    lo k [] = []
  wkArgs    lo k (x ∷ args) = wkArg lo k x ∷ wkArgs lo k args
  wkArg     lo k (arg i v)  = arg i (wk lo k v)
  wkSort    lo k (set t)    = set (wk lo k t)
  wkSort    lo k (lit n)    = lit n
  wkSort    lo k unknown    = unknown

  wkClauses lo k [] = []
  wkClauses lo k (c ∷ cs) = wkClause lo k c ∷ wkClauses lo k cs

  wkClause lo k (clause ps b)      = clause ps (wk (lo + patternBindings ps) k b)
  wkClause lo k (absurd-clause ps) = absurd-clause ps

-- Instances --

DeBruijnTraversable : ∀ {a} {F : Set a → Set a} {{_ : Functor F}} {{_ : Traversable F}}
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

  DeBruijnList : ∀ {a} {A : Set a} {{_ : DeBruijn A}} → DeBruijn (List A)
  DeBruijnList = DeBruijnTraversable

  DeBruijnVec : ∀ {a} {A : Set a} {{_ : DeBruijn A}} {n : Nat} → DeBruijn (Vec A n)
  DeBruijnVec = DeBruijnTraversable

  DeBruijnArg : {A : Set} {{_ : DeBruijn A}} → DeBruijn (Arg A)
  DeBruijnArg = DeBruijnTraversable

  DeBruijnMaybe : {A : Set} {{_ : DeBruijn A}} → DeBruijn (Maybe A)
  DeBruijnMaybe = DeBruijnTraversable
