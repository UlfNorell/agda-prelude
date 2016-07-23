module Prelude.Bytes where

open import Prelude.Bool
open import Prelude.Decidable
open import Prelude.Equality
open import Prelude.Equality.Unsafe

{-# IMPORT Data.ByteString #-}

postulate
  Bytes : Set
{-# COMPILED_TYPE Bytes Data.ByteString.ByteString #-}


private
  module Internal where
    postulate
      empty : Bytes
      append : Bytes → Bytes → Bytes
    {-# COMPILED empty Data.ByteString.empty #-}
    {-# COMPILED append Data.ByteString.append #-}

-- Eq --

private
  postulate eqBytes : Bytes → Bytes → Bool
  {-# COMPILED eqBytes (==) #-}

  decEqBytes : (x y : Bytes) → Dec (x ≡ y)
  decEqBytes x y with eqBytes x y
  ... | true = yes unsafeEqual
  ... | false = no unsafeNotEqual

instance
  EqBytes : Eq Bytes
  EqBytes = record { _==_ = decEqBytes }

-- Monoid --

instance
  open import Prelude.Monoid
  MonoidBytes : Monoid Bytes
  MonoidBytes = record { mempty = Internal.empty; _<>_ = Internal.append }


