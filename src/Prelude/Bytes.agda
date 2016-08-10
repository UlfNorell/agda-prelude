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

instance
  EqBytes : Eq Bytes
  _==_ {{EqBytes}} x y with eqBytes x y
  ... | true = yes unsafeEqual
  ... | false = no unsafeNotEqual

-- Monoid --

instance
  open import Prelude.Monoid
  MonoidBytes : Monoid Bytes
  mempty {{MonoidBytes}} = Internal.empty
  _<>_   {{MonoidBytes}} = Internal.append
