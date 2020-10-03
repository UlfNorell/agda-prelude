module Container.BinaryTree.RedBlack where

open import Container.BinaryTree.Base

open import Agda.Primitive
open import Prelude.Product
open import Prelude.Function
open import Prelude.Functor
open import Prelude.List hiding (insert)
open import Prelude.Ord
open import Prelude.Maybe
open import Prelude.Variables
import Container.BinaryTree.Ordered as Ord

data Color : Set where
    red : Color
    black : Color



-- We don't put any constraints in the type level Breaking the red-black
-- property externaly

RedBlackTree : ∀ {ℓ} → Set ℓ → Set ℓ
RedBlackTree A = BinaryTree (Color × A)


lookupBy : {{_ : Ord B}} → (A → B) → B → RedBlackTree A → Maybe A
lookupBy proj key t = fmap snd (Ord.binarySearchBy (proj ∘ snd) key t)


-- left and right balance does not hold definitionally, I let it be since it does not matter
leftBalance : Color → A
            → RedBlackTree A →  RedBlackTree A
            → RedBlackTree A
leftBalance black z (node (red , y) (node (red , x) a b) c) d =
  node (red , y) (node (black , x) a b) (node (black , z) c d)
leftBalance black z (node (red , x) a (node (red , y) b c)) d
  =  node (red , y) (node (black , x) a b) (node (black , z) c d)
leftBalance color value l r = node (color , value) l r

rightBalance : Color → A
             → RedBlackTree A → RedBlackTree A
             → RedBlackTree A
rightBalance black x a (node (red , z) (node (red , y) b c) d)
  = node (red , y) (node (black , x) a b) (node (black , z) c d)
rightBalance black x a (node (red , y) b (node (red , z) c d))
  = node (red , y) (node (black , x) a b) (node (black , z) c d)
rightBalance color v l r = node (color , v) l r

-- B should be equivalent to (p A), for efficiency
insertInner : {{_ : Ord B}} → (A → B) → B → A → RedBlackTree A → RedBlackTree A
insertInner p b a leaf = node (red , a) leaf leaf
insertInner p b a t@(node (color , a') l r)
  with compare b (p a')
...| less    _ = leftBalance color a' (insertInner p b a l) r
...| greater _ = rightBalance color a' l (insertInner p b a r)
...| equal   _ = (node (color , a) l r)

insertBy : {{_ : Ord B}} → (A → B) → A → RedBlackTree A → RedBlackTree A
insertBy p a t =
  case insertInner p (p a) a t of
    λ {  leaf → leaf
       ; (node (_ , a') l r) → node (black , a') l r
       }

fromListBy : {{_ : Ord B}} → (A → B) → List A → RedBlackTree A
fromListBy p = foldl (flip (insertBy p)) leaf
