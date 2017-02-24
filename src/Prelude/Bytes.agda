module Prelude.Bytes where

open import Prelude.Bool
open import Prelude.Decidable
open import Prelude.Equality
open import Prelude.Equality.Unsafe

{-# FOREIGN GHC import qualified Data.ByteString as B #-}

postulate
  Bytes : Set
{-# COMPILE GHC Bytes = type B.ByteString #-}


private
  module Internal where
    postulate
      empty : Bytes
      append : Bytes → Bytes → Bytes
    {-# COMPILE GHC empty  = B.empty #-}
    {-# COMPILE GHC append = B.append #-}

-- Eq --

private
  postulate eqBytes : Bytes → Bytes → Bool
  {-# COMPILE GHC eqBytes = (==) #-}

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
