module Container.Dictionary where

import Container.BinaryTree.RedBlack as RB
import Container.BinaryTree.Base as BT
open import Container.BinaryTree.Relations

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
-- concrete implementation is a red-black binary tree.
record Dictionary {a b} (K : Set a) (V : Set b) : Set (a ⊔ b) where
  field
    unwrap : RB.RedBlackTree {a ⊔ b} (K × V)

module _ {a b} {K : Set a} {V : Set b} {{_ : Ord K}} where

  get : K → Dictionary K V → Maybe V
  get k d = fmap′ snd (RB.lookupBy fst k (Dictionary.unwrap d))

  set : K → V → Dictionary K V → Dictionary K V
  set k v d = record { unwrap = RB.insertBy fst (k , v) (Dictionary.unwrap d) }

  remove : K → Dictionary K V → Dictionary K V
  remove k d =
    record { unwrap =
      RB.deleteProj fst k (Dictionary.unwrap d)
    }

  keys : Dictionary K V → List K
  keys d = BT.inorderFold (_∷_ ∘ (fst ∘ snd)) [] (Dictionary.unwrap d)

  values : Dictionary K V → List V
  values d = BT.inorderFold (_∷_ ∘ (snd ∘ snd)) [] (Dictionary.unwrap d)

  empty : Dictionary K V
  empty = record { unwrap = BT.leaf }

  size : Dictionary K V → Nat
  size = BT.size ∘ Dictionary.unwrap
