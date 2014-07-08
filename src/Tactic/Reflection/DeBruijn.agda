
module Tactic.Reflection.DeBruijn where

open import Prelude
open import Builtin.Reflection

record DeBruijn {a} (A : Set a) : Set a where
  field
    strFrom : (from n : Nat) → A → Maybe A
    weakenFrom     : (from n : Nat) → A → A

  strengthen : Nat → A → Maybe A
  strengthen 0 = just
  strengthen n = strFrom 0 n

  weaken : Nat → A → A
  weaken zero = id
  weaken n    = weakenFrom 0 n

open DeBruijn {{...}} public

private
  Str : Set → Set
  Str A = Nat → Nat → A → Maybe A

  strArgs    : Str (List (Arg Term))
  strArg     : Str (Arg Term)
  strArgType : Str (Arg Type)
  strType    : Str Type

  strTerm : Str Term
  strTerm lo n (var x args) =
    if      x < lo     then var x <$> strArgs lo n args
    else if x < lo + n then nothing
    else                    var (x - n) <$> strArgs lo n args
  strTerm lo n (con c args)  = con c <$> strArgs lo n args
  strTerm lo n (def f args)  = def f <$> strArgs lo n args
  strTerm lo n (lam v t)     = lam v <$> strTerm (suc lo) n t
  strTerm lo n (pi a b)      = pi    <$> strArgType lo n a <*> strType (suc lo) n b
  strTerm lo n (sort x)      = just (sort x)  -- todo strSort
  strTerm lo n (lit l)       = just (lit l)
  strTerm lo n (pat-lam _ _) = just unknown -- todo
  strTerm lo n unknown       = just unknown

  strArgs    lo n []         = just []
  strArgs    lo n (x ∷ args) = _∷_   <$> strArg  lo n x <*> strArgs lo n args
  strArg     lo n (arg i v)  = arg i <$> strTerm lo n v
  strArgType lo n (arg i v)  = arg i <$> strType lo n v
  strType    lo n (el s v)   = el s  <$> strTerm lo n v  -- todo strSort

private
  Wk : Set → Set
  Wk A = Nat → Nat → A → A

  wkArgs    : Wk (List (Arg Term))
  wkArg     : Wk (Arg Term)
  wkArgType : Wk (Arg Type)
  wkType    : Wk Type

  wk : Wk Term
  wk lo k (var x args) =
    if x < lo then var x       (wkArgs lo k args)
    else           var (x + k) (wkArgs lo k args)
  wk lo k (con c args)  = Term.con c $ wkArgs lo k args
  wk lo k (def f args)  = def f $ wkArgs lo k args
  wk lo k (lam v t)     = lam v $ wk (suc lo) k t
  wk lo k (pi a b)      = pi (wkArgType lo k a) (wkType (suc lo) (suc k) b)
  wk lo k (sort x)      = sort x  -- todo wkSort
  wk lo k (lit l)       = lit l
  wk lo k (pat-lam _ _) = unknown -- todo
  wk lo k unknown       = unknown

  wkArgs    lo k [] = []
  wkArgs    lo k (x ∷ args) = wkArg lo k x ∷ wkArgs lo k args
  wkArg     lo k (arg i v)  = arg i (wk lo k v)
  wkArgType lo k (arg i v)  = arg i (wkType lo k v)
  wkType    lo k (el s v)   = el s (wk lo k v)  -- todo wkSort

-- Instances --

DeBruijnTerm : DeBruijn Term
DeBruijnTerm = record { strFrom = strTerm ; weakenFrom = wk }

DeBruijnType : DeBruijn Type
DeBruijnType = record { strFrom = strType ; weakenFrom = wkType }

DeBruijnArgs : DeBruijn (List (Arg Term))
DeBruijnArgs = record { strFrom = strArgs ; weakenFrom = wkArgs }

DeBruijnArgType : DeBruijn (Arg Type)
DeBruijnArgType = record { strFrom = strArgType ; weakenFrom = wkArgType }
