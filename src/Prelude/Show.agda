
module Prelude.Show where

open import Prelude.String
open import Prelude.Char
open import Prelude.Nat
open import Prelude.Int
open import Prelude.Word
open import Prelude.Function
open import Prelude.List
open import Prelude.Fin
open import Prelude.Vec
open import Prelude.Maybe
open import Prelude.Sum
open import Prelude.Product
open import Prelude.Bool
open import Prelude.Ord
open import Prelude.Semiring

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

  shows : A → ShowS
  shows = showsPrec 0

open Show {{...}} public

simpleShowInstance : ∀ {a} {A : Set a} → (A → String) → Show A
showsPrec {{simpleShowInstance s}} _ x = showString (s x)

ShowBy : ∀ {a b} {A : Set a} {B : Set b} {{ShowB : Show B}} → (A → B) → Show A
showsPrec {{ShowBy f}} p = showsPrec p ∘ f

--- Instances ---

-- Bool --

instance
  ShowBool : Show Bool
  ShowBool = simpleShowInstance λ b → if b then "true" else "false"

-- Int --

instance
  ShowInt : Show Int
  ShowInt = simpleShowInstance primShowInteger

-- Nat --

instance
  ShowNat : Show Nat
  ShowNat = simpleShowInstance (primShowInteger ∘ pos)

-- Word64 --

instance
  ShowWord64 : Show Word64
  ShowWord64 = simpleShowInstance (show ∘ word64ToNat)

-- Char --

instance
  ShowChar : Show Char
  ShowChar = simpleShowInstance primShowChar

-- String --

instance
  ShowString : Show String
  ShowString = simpleShowInstance primShowString

-- List --

instance
  ShowList : ∀ {a} {A : Set a} {{ShowA : Show A}} → Show (List A)
  showsPrec {{ShowList}} _ []       = showString "[]"
  showsPrec {{ShowList}} _ (x ∷ xs) =
    showString "["
    ∘ foldl (λ r x → r ∘ showString ", " ∘ showsPrec 2 x) (showsPrec 2 x) xs
    ∘ showString "]"

-- Fin --

instance
  ShowFin : ∀ {n} → Show (Fin n)
  ShowFin = simpleShowInstance (show ∘ finToNat)

-- Vec --

instance
  ShowVec : ∀ {a} {A : Set a} {n} {{ShowA : Show A}} → Show (Vec A n)
  ShowVec = ShowBy vecToList

-- Maybe --

instance
  ShowMaybe : ∀ {a} {A : Set a} {{ShowA : Show A}} → Show (Maybe A)
  showsPrec {{ShowMaybe}} p nothing  = showString "nothing"
  showsPrec {{ShowMaybe}} p (just x) = showParen (p >? 9) (showString "just " ∘ showsPrec 10 x)

-- Either --

instance
  ShowEither : ∀ {a b} {A : Set a} {B : Set b} {{ShowA : Show A}} {{ShowB : Show B}} → Show (Either A B)
  showsPrec {{ShowEither}} p (left  x) = showParen (p >? 9) $ showString "left " ∘ showsPrec 10 x
  showsPrec {{ShowEither}} p (right x) = showParen (p >? 9) $ showString "right " ∘ showsPrec 10 x

-- Sigma --

instance
  ShowSigma : ∀ {a b} {A : Set a} {B : A → Set b} {{ShowA : Show A}} {{ShowB : ∀ {x} → Show (B x)}} →
                Show (Σ A B)
  showsPrec {{ShowSigma}} p (x , y) = showParen (p >? 1) $ showsPrec 2 x ∘ showString ", " ∘ showsPrec 1 y
