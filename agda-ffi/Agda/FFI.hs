
module Agda.FFI where

type AgdaList   l     = []
type AgdaMaybe  l     = Maybe
type AgdaEither la lb = Either

data Strict l a = Strict !a

