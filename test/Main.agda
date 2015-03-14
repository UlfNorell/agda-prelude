
open import Prelude
open import Data.Traversable
open import Data.Monoid
open import Data.Foldable
open import Data.List
open import Text.Parse
open import Text.Lex
open import Text.Printf
open import Control.Monad.State
open import Control.WellFounded
open import Builtin.Size
open import Builtin.Coinduction
open import Builtin.Float
open import Builtin.Reflection

open import Tactic.Reflection.DeBruijn
open import Tactic.Reflection.Equality
open import Tactic.Reflection.Free
open import Tactic.Reflection.Quote
open import Tactic.Reflection.Telescope
open import Tactic.Deriving.Eq

open import Data.Nat.DivMod
open import Data.Nat.GCD

Hello = printf "%c%s" 'H' "ello"
World = printf "%6s" "World"

M = StateT Nat IO

putStrI : String → StateT Nat IO Unit
putStrI s = get >>= λ n →
            put (suc n) >>
            lift (putStr (printf "%d%s" n s))

main : IO ⊤
main = _ <$ (runStateT (mapM putStrI (Hello ∷ World ∷ " " ∷ [])) 0 >>
             putStr (show (432429 divmod 41)) >>
             putStr (" " & show (gcd! (19 * 17 * 31) (31 * 5))) >>
             putStrLn "")
