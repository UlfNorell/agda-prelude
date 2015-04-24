
module Prelude.Number where

open import Prelude.Nat.Core

record Number {a} (A : Set a) : Set a where
  field fromNat : Nat → A

open Number {{...}} public

{-# BUILTIN FROMNAT fromNat #-}

record Negative {a} (A : Set a) : Set a where
  field fromNeg : Nat → A

open Negative {{...}} public

{-# BUILTIN FROMNEG fromNeg #-}
