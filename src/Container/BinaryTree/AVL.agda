module Container.BinaryTree.AVL where

open import Prelude.Function
open import Prelude.Equality
open import Prelude.Product
open import Prelude.Unit
open import Prelude.Empty

open import Prelude.Ord

open import Prelude.Variables

open import Container.BinaryTree.Base

data Balance : Set where
  neg : Balance
  zero : Balance
  pos  : Balance

BalanceLessThan : Balance → Balance → Set
BalanceLessThan neg zero = ⊤
BalanceLessThan neg pos = ⊤
BalanceLessThan zero pos = ⊤
BalanceLessThan neg neg = ⊥
BalanceLessThan zero zero = ⊥
BalanceLessThan pos pos = ⊥
BalanceLessThan pos neg = ⊥
BalanceLessThan pos zero = ⊥
BalanceLessThan zero neg = ⊥



compareBalance : (x : Balance) → (y : Balance) → Comparison BalanceLessThan x y
compareBalance neg zero = less unit
compareBalance neg pos = less unit
compareBalance zero pos = less unit
compareBalance neg neg = equal refl
compareBalance zero zero = equal refl
compareBalance pos pos = equal refl
compareBalance pos neg = greater unit
compareBalance pos zero = greater unit
compareBalance zero neg = greater unit


AVL : ∀ {ℓ} → Set ℓ → Set ℓ
AVL A = BinaryTree (Balance × A)

singleton : A → AVL A
singleton a = node (zero , a) leaf leaf

insert : {{_ : Ord A}} → A → AVL A → AVL A
insert x leaf = singleton x
insert x (node (b , y) l r) =
  case compare x y of
    λ { (equal eq) → node (b , x) l r
      ; (less lt) →  {!!}
      ; (greater gt) → {!!}
      }
