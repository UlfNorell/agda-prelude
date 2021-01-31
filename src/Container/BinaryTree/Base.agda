module Container.BinaryTree.Base where

open import Prelude.Nat
open import Prelude.Maybe
open import Prelude.Semiring
open import Prelude.Ord

open import Prelude.Applicative
open import Prelude.Monad
open import Container.Foldable

open import Prelude.Functor

open import Prelude.Variables

-- Just the data structure of a binary tree. We enforce order and such by other
-- means, giving the user flexibility.
data BinaryTree {a} (A : Set a) : Set a where
  leaf : BinaryTree A
  node : A → BinaryTree A → BinaryTree A → BinaryTree A

size : BinaryTree A → Nat
size leaf = 0
size (node _ l r) = 1 + size l + size r

height : BinaryTree A → Nat
height leaf = 0
height (node _ l r) = 1 + max (height l) (height r)


leftChild : BinaryTree A → Maybe (BinaryTree A)
leftChild leaf = nothing
leftChild (node _ l _) = just l

rightChild : BinaryTree A → Maybe (BinaryTree A)
rightChild leaf = nothing
rightChild (node _ _ r) = just r

map : (A → B) → BinaryTree A → BinaryTree B
map _ leaf = leaf
map f (node a l r) = node (f a) (map f l) (map f r)

instance
  FunctorBinaryTree : Functor (BinaryTree {ℓ})
  fmap {{FunctorBinaryTree}} = map


-- Traversals --

module _ {F : Set ℓ → Set ℓ₁} {{AppF : Applicative F}} where
  preorderTraverse :  (A → F B) → BinaryTree A → F (BinaryTree  B)
  preorderTraverse f leaf = pure leaf
  preorderTraverse f (node a l r) =
    ⦇ (λ a' l' r' → node a' l' r')
       (f a)
       (preorderTraverse f l)
       (preorderTraverse f r)
     ⦈

  inorderTraverse : (A → F B) → BinaryTree A → F (BinaryTree B)
  inorderTraverse f leaf = pure leaf
  inorderTraverse f (node a l r) =
    ⦇ (λ l' a' r' → node a' l' r')
      (inorderTraverse f l)
      (f a)
      (inorderTraverse f r)
    ⦈

  postorderTraverse : (A → F B) → BinaryTree A → F (BinaryTree B)
  postorderTraverse f leaf = pure leaf
  postorderTraverse f (node a l r) =
    ⦇ (λ l' r' a' → node a' l' r')
      (inorderTraverse f l)
      (inorderTraverse f r)
      (f a)
    ⦈



-- Folds --

preorderFold : (A → B → B) → B → BinaryTree A → B
preorderFold f b leaf = b
preorderFold f b (node a l r) = preorderFold f (preorderFold f (f a b) l) r

inorderFold : (A → B → B) → B → BinaryTree A → B
inorderFold f b leaf = b
inorderFold f b (node a l r) = inorderFold f (f a (inorderFold f b l)) r

postorderFold : (A → B → B) → B → BinaryTree A → B
postorderFold f b leaf = b
postorderFold f b (node a l r) = f a (postorderFold f (postorderFold f b l) r)

-- instance
--  FoldableBinTree : ∀ {a w} → Foldable {a = a} {w = w} (BinaryTree {a})
--  foldMap {{FoldableBinTree}} f = inorderFold f

module _ {M : Set ℓ → Set ℓ₁} {{_ : Monad M}} where
  preorderFoldM : (A → B → M B) → B → BinaryTree A → M B
  preorderFoldM f b leaf = pure b
  preorderFoldM f b (node a l r) = do
    mid ← f a b
    left ← preorderFoldM f mid l
    preorderFoldM f left r

  inorderFoldM : (A → B → M B) → B → BinaryTree A → M B
  inorderFoldM f b leaf = pure b
  inorderFoldM f b (node a l r) = do
    left ← inorderFoldM f b l
    mid ← f a left
    inorderFoldM f mid r

  postorderFoldM : (A → B → M B) → B → BinaryTree A → M B
  postorderFoldM f b leaf = pure b
  postorderFoldM f b (node a l r) = do
   left ← postorderFoldM f b l
   right ← postorderFoldM f left r
   f a right
