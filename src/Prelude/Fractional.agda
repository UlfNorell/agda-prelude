
module Prelude.Fractional where

open import Agda.Primitive

record Fractional {a} (A : Set a) : Set (lsuc a) where
  infixl 7 _/_
  field
    Constraint : A → A → Set a
    _/_ : (x y : A) {{_ : Constraint x y}} → A

open Fractional {{...}} using (_/_) public
{-# DISPLAY Fractional._/_ _ x y = x / y #-}
