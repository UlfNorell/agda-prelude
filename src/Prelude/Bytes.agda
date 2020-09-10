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
  open import Prelude.Semigroup

  SemigroupBytes : Semigroup Bytes
  _<>_ {{SemigroupBytes}} = Internal.append

  MonoidBytes : Monoid Bytes
  Monoid.super MonoidBytes = SemigroupBytes
  mempty {{MonoidBytes}} = Internal.empty
