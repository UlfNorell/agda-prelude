
module Prelude.Unit where

record ⊤ : Set where
  constructor tt

-- To keep changes from maint-2.4.0 to a minimum.
Unit = ⊤

record ⊤′ {a} : Set a where
  constructor tt

{-# COMPILED_DATA ⊤ () () #-}
