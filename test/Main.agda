
open import Prelude
open import Data.Traversable
open import Data.Monoid
open import Data.Foldable
open import Data.List
open import Text.Parse
open import Text.Lex

main : IO Unit
main = _ <$ mapM putStr ("Hello" ∷ " World" ∷ "\n" ∷ [])
