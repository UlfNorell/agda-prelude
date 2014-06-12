
module Prelude.Unit where

record ⊤ : Set where
  constructor tt

{-# COMPILED_DATA ⊤ () () #-}

Unit = ⊤
