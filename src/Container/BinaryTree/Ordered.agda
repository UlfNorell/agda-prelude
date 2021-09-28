-- Contains generic operations for ordered binary trees

module Container.BinaryTree.Ordered where

open import Container.BinaryTree.Base

open import Agda.Primitive
open import Prelude.Ord
open import Prelude.Maybe
open import Prelude.Variables

-- Ordered insert a'la ordered binary tree
insertBy : {{_ : Ord B}} → (A → B) → A → BinaryTree A → BinaryTree A
insertBy toB x leaf = node x leaf leaf
insertBy toB x (node y l r)
  with compare (toB x) (toB y)
...| less _ = node y (insertBy toB x l) r
...| greater _ = node y l (insertBy toB x r)
...| equal _ = node y l r

-- Ordered member a'la ordered binary search tree
binarySearchBy : {{_ : Ord B}} → (A → B) → B → BinaryTree A → Maybe A
binarySearchBy toB _ leaf = nothing
binarySearchBy toB x (node y l r)
  with compare x (toB y)
...| equal _ = just y
...| less _ = binarySearchBy toB x l
...| greater _ = binarySearchBy toB x r
