module Container.Dictionary where

open import Container.BinaryTree.RedBlack
import Container.BinaryTree.Base as BT

open import Agda.Primitive
open import Prelude.Variables
open import Prelude.Product
open import Prelude.Maybe
open import Prelude.Nat
open import Prelude.Functor
open import Prelude.Function

open import Prelude.List

open import Prelude.Ord

-- This type in not intended as any specific implementation. The current
-- concrete implementation is a red-black tree.
record Dictionary {a b} (K : Set a) (V : Set b) : Set (a ⊔ b) where
  field
    unwrap : RedBlackTree {a ⊔ b} (K × V)

module _ {a b} {K : Set a} {V : Set b} {{_ : Ord K}} where
  get : K → Dictionary K V → Maybe V
  get k d =
    case (lookupBy fst k (Dictionary.unwrap d)) of
      λ { nothing → nothing ; (just (_ , v)) → just v}

  set : K → V → Dictionary K V → Dictionary K V
  set k v d = record { unwrap = insertBy fst (k , v) (Dictionary.unwrap d) }

  keys : Dictionary K V → List K
  keys d = BT.inorderFold (_∷_ ∘ (fst ∘ snd)) [] (Dictionary.unwrap d)

  values : Dictionary K V → List V
  values d = BT.inorderFold (_∷_ ∘ (snd ∘ snd)) [] (Dictionary.unwrap d)

  size : Dictionary K V → Nat
  size = BT.size ∘ Dictionary.unwrap
