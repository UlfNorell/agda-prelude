
module Builtin.Size where

postulate
  Size   : Set
  Size<_ : Size → Set
  ↑_     : Size → Size
  ω      : Size

{-# BUILTIN SIZE    Size   #-}
{-# BUILTIN SIZELT  Size<_ #-}
{-# BUILTIN SIZESUC ↑_     #-}
{-# BUILTIN SIZEINF ω      #-}
