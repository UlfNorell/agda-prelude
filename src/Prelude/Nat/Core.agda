
module Prelude.Nat.Core where

open import Prelude.Unit
open import Prelude.Empty
open import Prelude.Number
open import Prelude.Semiring

open import Agda.Builtin.Nat public
  renaming ( _+_        to _+N_
           ; _*_        to _*N_
           ; _-_        to _-N_
           ; _==_       to eqNat
           ; _<_        to lessNat
           ; div-helper to divAux
           ; mod-helper to modAux )

{-# DISPLAY _+N_ = _+_ #-}
{-# DISPLAY _-N_ = _-_ #-}
{-# DISPLAY _*N_ = _*_ #-}

--- Semiring ---

instance
  NumberNat : Number Nat
  Number.Constraint NumberNat _ = ⊤
  Number.fromNat    NumberNat n = n

  SemiringNat : Semiring Nat
  zro {{SemiringNat}} = 0
  one {{SemiringNat}} = 1
  _+_ {{SemiringNat}} = _+N_
  _*_ {{SemiringNat}} = _*N_

  SubtractiveNat : Subtractive Nat
  _-_    {{SubtractiveNat}}   = _-N_
  negate {{SubtractiveNat}} _ = 0

--- Division and modulo ---

NonZero : Nat → Set
NonZero zero    = ⊥
NonZero (suc _) = ⊤

infixl 7 natDiv natMod
syntax natDiv m n = n div m
natDiv : (m : Nat) {{nz : NonZero m}} → Nat → Nat
natDiv zero {{}} n
natDiv (suc m) n = divAux 0 m n m

syntax natMod m n = n mod m
natMod : (m : Nat) {{nz : NonZero m}} → Nat → Nat
natMod zero {{}} n
natMod (suc m) n = modAux 0 m n m

{-# INLINE natMod #-}
{-# INLINE natDiv #-}
