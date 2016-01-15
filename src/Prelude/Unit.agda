
module Prelude.Unit where

record ⊤ : Set where
  instance
    constructor tt

{-# BUILTIN UNIT ⊤ #-}

-- To keep changes from compat-2.4.0 to a minimum.
Unit = ⊤
pattern unit = tt

record ⊤′ {a} : Set a where
  instance constructor tt

{-# COMPILED_DATA ⊤ () () #-}
