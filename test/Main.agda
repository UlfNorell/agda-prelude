
open import Prelude
open import Data.Traversable
open import Data.Monoid

main : IO ⊤
main = _ <$ mapM putStrLn ("Hello" ∷ "World!" ∷ [])
