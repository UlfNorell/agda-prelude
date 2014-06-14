
open import Prelude
open import Data.Traversable
open import Data.Monoid
open import Data.Foldable
open import Data.List
open import Text.Parse
open import Text.Lex
open import Text.Printf

Hello = printf "%c%s" 'H' "ello"
World = printf "%6s" "World"

main : IO ⊤
main = _ <$ mapM putStr (Hello ∷ World ∷ "\n" ∷ [])
