
module _ where

open import Prelude
open import Data.Nat.Prime

main : IO ⊤
main = print $ isPrime! 17592186044423
