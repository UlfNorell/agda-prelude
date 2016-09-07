
module _ where

open import Prelude
open import Numeric.Nat.Prime

2^44+7 2^46+15 2^48+21 : Nat
2^44+7  =  17592186044423
2^46+15 =  70368744177679
2^48+21 = 281474976710677

main : IO ⊤
main = print $ isPrime! 2^48+21
