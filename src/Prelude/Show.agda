
module Prelude.Show where

open import Prelude.String
open import Prelude.Char
open import Prelude.Nat
open import Prelude.Function
open import Prelude.List
open import Prelude.Fin
open import Prelude.Vec
open import Prelude.Maybe
open import Prelude.Sum
open import Prelude.Product
open import Prelude.Bool
open import Prelude.Ord

--- Class ---

ShowS = String → String

showString : String → ShowS
showString s r = s & r

showParen : Bool → ShowS → ShowS
showParen false s = s
showParen true  s = showString "(" ∘ s ∘ showString ")"

record Show {a} (A : Set a) : Set a where
  field
    showsPrec : Nat → A → ShowS

  show : A → String
  show x = showsPrec 0 x ""

open Show {{...}} public

simpleShowInstance : ∀ {a} {A : Set a} → (A → String) → Show A
simpleShowInstance s = record { showsPrec = λ _ x r → s x & r }

--- Instances ---

-- Bool --

ShowBool : Show Bool
ShowBool = simpleShowInstance λ b → if b then "true" else "false"

-- Nat --

private
  digit : Nat → Char
  digit n = natToChar (n + charToNat '0')

  {-# NO_TERMINATION_CHECK #-}
  showNat′ : Nat → List Char → List Char
  showNat′ 0 ds = ds
  showNat′ n ds = showNat′ (n div 10) (digit (n mod 10) ∷ ds)

  showNat : Nat → String
  showNat zero = "0"
  showNat n = packString $ showNat′ n []

ShowNat : Show Nat
ShowNat = simpleShowInstance showNat

-- Char --

primitive
  primShowChar : Char → String

ShowChar : Show Char
ShowChar = simpleShowInstance primShowChar

-- String --

primitive
  primShowString : String → String

ShowString : Show String
ShowString = simpleShowInstance primShowString

-- List --

private
  showList : ∀ {a} {A : Set a} {{ShowA : Show A}} → Nat → List A → ShowS
  showList _ []       = showString "[]"
  showList _ (x ∷ xs) = showString "["
                      ∘ foldl (λ r x → r ∘ showString ", " ∘ showsPrec 2 x) (showsPrec 2 x) xs
                      ∘ showString "]"

ShowList : ∀ {a} {A : Set a} {{ShowA : Show A}} → Show (List A)
ShowList = record { showsPrec = showList }

-- Fin --

ShowFin : ∀ {n} → Show (Fin n)
ShowFin = simpleShowInstance (show ∘ finToNat)

-- Vec --

ShowVec : ∀ {a} {A : Set a} {n} {{ShowA : Show A}} → Show (Vec A n)
ShowVec {A = A} = record { showsPrec = λ p → showsPrec p ∘ vecToList }
  where ShowListA : Show (List A)
        ShowListA = ShowList

-- Maybe --

private
  showMaybe : ∀ {a} {A : Set a} {{ShowA : Show A}} → Nat → Maybe A → ShowS
  showMaybe p nothing  = showString "nothing"
  showMaybe p (just x) = showParen (p > 9) (showString "just " ∘ showsPrec 10 x)

ShowMaybe : ∀ {a} {A : Set a} {{ShowA : Show A}} → Show (Maybe A)
ShowMaybe = record { showsPrec = showMaybe }

-- Either --

private
  showEither : ∀ {a b} {A : Set a} {B : Set b} {{ShowA : Show A}} {{ShowB : Show B}} →
               Nat → Either A B → ShowS
  showEither p (left  x) = showParen (p > 9) $ showString "left " ∘ showsPrec 10 x
  showEither p (right x) = showParen (p > 9) $ showString "right " ∘ showsPrec 10 x

ShowEither : ∀ {a b} {A : Set a} {B : Set b} {{ShowA : Show A}} {{ShowB : Show B}} → Show (Either A B)
ShowEither = record { showsPrec = showEither }

-- Sigma --

private
  showPair : ∀ {a b} {A : Set a} {B : A → Set b} {{ShowA : Show A}} {{ShowB : ∀ {x} → Show (B x)}} →
               Nat → Σ A B → ShowS
  showPair p (x , y) = showParen (p > 1) $ showsPrec 2 x ∘ showString ", " ∘ showsPrec 1 y

ShowSigma : ∀ {a b} {A : Set a} {B : A → Set b} {{ShowA : Show A}} {{ShowB : ∀ {x} → Show (B x)}} → Show (Σ A B)
ShowSigma = record { showsPrec = showPair }
