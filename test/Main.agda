
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

Hello = printf "%c%s" 'H' "ello"
World = printf "%6s" "World"

M = StateT Nat IO

MonadM : Monad M
MonadM = MonadStateT

ApplicativeM : Applicative M
ApplicativeM = ApplicativeStateT

putStrI : String → StateT Nat IO Unit
putStrI s = get >>= λ n →
            put (suc n) >>
            lift (putStr (printf "%d%s" n s))

main : IO ⊤
main = _ <$ runStateT (mapM putStrI (Hello ∷ World ∷ "\n" ∷ [])) 0
