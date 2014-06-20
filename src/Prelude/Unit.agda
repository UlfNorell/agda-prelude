
module Prelude.Unit where

record ⊤ : Set where
  constructor tt

-- Agda-2.4.0 does not allow COMPILED_DATA for records #-}
data Unit : Set where
  tt : Unit

record ⊤′ {a} : Set a where
  constructor tt

{-# COMPILED_DATA Unit () () #-}
