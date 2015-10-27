
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
open import Tactic.Nat

open import Data.Nat.DivMod
open import Data.Nat.Divide
open import Data.Nat.GCD
open import Data.Nat.Prime
open import Data.Rational
open import Data.Nat.Modulo
open import Data.Nat.Pow
open import Data.Smashed

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

downFrom : Nat → List Nat
downFrom  zero   = []
downFrom (suc n) = suc n ∷ downFrom n

thm : ∀ n → 6 * sum (map (_^ 2) (downFrom n)) ≡ n * (n + 1) * (2 * n + 1)
thm = induction

thm₂ : (a b : Nat) → (a - b) * (a + b) ≡ a ^ 2 - b ^ 2
thm₂ a b = auto

data N : Set where
  z : N
  s : N → N

eqN : unquote (deriveEqType (quote N))
instance
  EqN : Eq N
  EqN = record { _==_ = eqN }
unquoteDef eqN = deriveEqDef (quote N)
