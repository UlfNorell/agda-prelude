module Prelude.Sized where

open import Prelude.Function
open import Prelude.Nat
open import Prelude.Variables

-- A typeclass for everything that has a "Natural size".
-- Ment to simplify code, not to be theoretical.
record Sized {a} (A : Set a) : Set a where
  field
    size : A → Nat
open Sized {{...}}

instance
  SizedNat : Sized Nat
  size {{SizedNat}} = id
