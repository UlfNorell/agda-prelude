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


module Insert where
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
  rightBalance black x a (node (red , z) (node (red , y) b c) d) =
    node (red , y) (node (black , x) a b) (node (black , z) c d)
  rightBalance black x a (node (red , y) b (node (red , z) c d)) =
    node (red , y) (node (black , x) a b) (node (black , z) c d)
  rightBalance color v l r = node (color , v) l r

  -- B should be equivalent to (p A), for efficiency
  insertInner : {{_ : Ord B}} → (A → B) → B → A → RedBlackTree A → RedBlackTree A
  insertInner p b a leaf = node (red , a) leaf leaf
  insertInner p b a t@(node (color , a') l r)
    with compare b (p a')
  ...| less    _ = leftBalance color a' (insertInner p b a l) r
  ...| greater _ = rightBalance color a' l (insertInner p b a r)
  ...| equal   _ = node (color , a) l r

insertBy : {{_ : Ord B}} → (A → B) → A → RedBlackTree A → RedBlackTree A
insertBy p a t =
  case Insert.insertInner p (p a) a t of
    λ {  leaf → leaf
       ; (node (_ , a') l r) → node (black , a') l r
       }


module Karhs where
  -- I'm a bit unsure about how the current insert operations works with
  -- deletion. I'm therefore using the balance operations as defined by Karh's
  -- 'Untyped' implementation

  -- Red-black trees with types. Journal of Functional Programming, 11(4), 425-432.
  -- (http://www.cs.ukc.ac.uk/people/staff/smk/redblack/rb.html)

  balance : RedBlackTree A → A → RedBlackTree A → RedBlackTree A
  balance (node (red , x) a b) y (node (red , z) c d) =
    node (red , y) (node (black , x) a b) (node (black , z) c d)
  balance (node (red , y) (node (red , x) a b) c) z d =
    node (red , y) (node (black , x) a b) (node (black , z) c d)
  balance (node (red , x) a (node (red , y) b c)) z d =
    node (red , y) (node (black , x) a b) (node (black , z) c d)
  balance a x (node (red , y) b (node (red , z) c d)) =
    node (red , y) (node (black , x) a b) (node (black , z) c d)
  balance a x (node (red , z) (node (red , y) b c) d) =
    node (red , y) (node (black , x) a b) (node (black , z) c d)
  balance a x b = node (black , x) a b

  -- Second case not defined by khars. we make it id
  sub1 : RedBlackTree A → RedBlackTree A
  sub1 (node (black , x) a b) = node (red , x) a b
  sub1 o = o

  balleft : RedBlackTree A → A → RedBlackTree A → RedBlackTree A
  balleft (node (red , x) a b) y c = node (red , y) (node (black , x) a b) c
  balleft bl x (node (black , y) a b) = balance bl x (node (red , y) a b)
  balleft bl x (node (red , z) (node (black , y) a b) c) =
    node (red , y) (node (black , x) bl a) (balance b z (sub1 c))
  balleft bl x br = node (red , x) bl br -- Case undefined in Kahr's

  balright : RedBlackTree A → A → RedBlackTree A → RedBlackTree A
  balright a x (node (red , y) b c) = node (red , x) a (node (black , y) b c)
  balright (node (black , x) a b) y bl = balance (node (red , x) a b) y bl
  balright (node (red , x) a (node (black , y) b c)) z bl =
    node (red , y) (balance (sub1 a) x b) (node (black , z) c bl)
  balright bl x br = node (red ,  x) bl br -- Case undefined in Kahr's

  app : RedBlackTree A → RedBlackTree A → RedBlackTree A
  app leaf x = x
  app x leaf = x
  app (node (red , x) a b) (node (red , y) c d) =
    case app b c of
      λ { (node (red , z) b' c') →
                node (red , z) (node (red , x) a b')
                               (node (red , y) c' d)
        ; bc → node (red , x) a (node (red , y) bc d)
        }
  app (node (black , x) a b) (node (black , y) c d) =
    case app b c of
      λ { (node (red , z) b' c') →
                node (red , z) (node (black , x) a b')
                               (node (black , y) c' d)
        ; bc → balleft a x (node (black , y) bc d)
        }
  app a (node (red , x) b c) = node (red , x) (app a b) c
  app (node (red , x) a b) c = node (red , x) a (app b c)

  mutual
    delformLeft : {{_ : Ord B}} → (A → B) → B → RedBlackTree A → A → RedBlackTree A → RedBlackTree A
    delformLeft proj x a@(node (black , _) _ _) y b = balleft (del proj x a) y b
    delformLeft proj x a y b = node (black , y) (del proj x a) b

    delformRight : {{_ : Ord B}} → (A → B) → B → RedBlackTree A → A → RedBlackTree A → RedBlackTree A
    delformRight proj x a y b@(node (black , _) _ _) = balright a y (del proj x b)
    delformRight proj x a y b = node (red , y) a (del proj x b)

    del : {{_ : Ord B}} → (A → B) → B → RedBlackTree A → RedBlackTree A
    del proj x leaf = leaf
    del proj x (node (_ , y) a b) =
      case (compare x (proj y)) of
        λ { (less lt) → delformLeft proj x a y b
          ; (greater gt) → delformRight proj x a y b
          ; (equal eq) → app a b
          }

deleteProj : {{_ : Ord B}} → (A → B) → B → RedBlackTree A → RedBlackTree A
deleteProj proj x t =
  case Karhs.del proj x t of
    λ { (node (_ , y) l r) → node (black , y) l r
      ; leaf → leaf
      }

delete : {{_ : Ord B}} → (A → B) → A → RedBlackTree A → RedBlackTree A
delete proj x t = deleteProj proj (proj x) t

fromListBy : {{_ : Ord B}} → (A → B) → List A → RedBlackTree A
fromListBy p = foldl (flip (insertBy p)) leaf
