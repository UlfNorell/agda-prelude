
import Everything

open import Prelude
open import Container.Traversable
open import Container.Foldable
open import Container.List
open import Text.Parse
open import Text.Lex
open import Text.Printf
open import Control.Monad.State
open import Control.Monad.Transformer
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

open import Numeric.Nat.DivMod
open import Numeric.Nat.Divide
open import Numeric.Nat.GCD
open import Numeric.Nat.Prime
open import Numeric.Rational
open import Numeric.Nat.Modulo
open import Numeric.Nat.Pow

open import MonoidTactic

-- open import DeriveEqTest

Hello = printf "%c%s" 'H' "ello"
World = printf "%-7s(%.6f)" "World" π

M = StateT Nat IO

putStrI : String → StateT Nat IO Unit
putStrI s = do
  n ← get
  put (suc n)
  lift (putStr (printf "[%d] %s\n" n s))

main : IO ⊤
main = do
  runStateT (mapM putStrI (Hello ∷ World ∷ " " ∷ [])) 0
  putStr (show (432429 divmod 41))
  putStr ("\n" & show (gcd! (19 * 17 * 31) (31 * 5)))
  putStrLn ""

downFrom : Nat → List Nat
downFrom zero    = []
downFrom (suc n) = suc n ∷ downFrom n

thm : ∀ n → 6 * sumR (map (_^ 2) (downFrom n)) ≡ n * (n + 1) * (2 * n + 1)
thm = induction

thm₂ : (a b : Nat) → (a - b) * (a + b) ≡ a ^ 2 - b ^ 2
thm₂ a b = auto

data N : Set where
  z : N
  s : N → N

unquoteDecl eqN = deriveEq eqN (quote N)
