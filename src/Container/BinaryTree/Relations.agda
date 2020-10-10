module Container.BinaryTree.Relations where

open import Container.BinaryTree.Base

open import Prelude.Empty
open import Prelude.Equality
open import Prelude.Function
open import Prelude.Product
open import Prelude.Unit

open import Agda.Primitive
open import Agda.Builtin.Nat


open import Prelude.Variables


data RootRel {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} (R : A → A → Set ℓ₂) : BinaryTree A → BinaryTree A → Set (ℓ₁ ⊔ ℓ₂) where
  leafleaf : RootRel R leaf leaf
  leafnode : ∀ {x a b} → RootRel R leaf (node x a b)
  nodeleaf : ∀ {x a b} → RootRel R (node x a b) leaf
  nodenode : ∀ {x y a b c d} → R x y → RootRel R (node x a b) (node y c d)

data AllNodes {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} (R : A → BinaryTree A → BinaryTree A → Set ℓ₂) : BinaryTree A → Set (ℓ₁ ⊔ ℓ₂)  where
  leaf : AllNodes R leaf
  node : {x : A} {l r : BinaryTree A} → R x l r → AllNodes R l → AllNodes R r → AllNodes R (node x l r)

data AnyNode {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} (R : A → BinaryTree A → BinaryTree A → Set ℓ₂) : BinaryTree A → Set (ℓ₁ ⊔ ℓ₂)  where
  here : {x : A} {l r : BinaryTree A} → R x l r → AnyNode R (node x l r)
  inLeft : {x : A} {l r : BinaryTree A} → AnyNode R l → AnyNode R (node x l r)
  inRight : {x : A} {l r : BinaryTree A} → AnyNode R r → AnyNode R (node x l r)


module _ {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} where
  Any : (R : A → Set ℓ₂) → BinaryTree A → Set (ℓ₁ ⊔ ℓ₂)
  Any R = AnyNode (λ x _ _ → R x)

  All : (R : A → Set ℓ₂) → BinaryTree A → Set (ℓ₁ ⊔ ℓ₂)
  All R = AllNodes (λ x _ _ → R x)

Member : ∀ {ℓ} → {A : Set ℓ} → (x : A) → BinaryTree A → Set ℓ
Member x = Any (_≡ x)

-- For relations depending on some child
data OnNode {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} (R : A → BinaryTree A → BinaryTree A → Set ℓ₂) : BinaryTree A → Set (ℓ₁ ⊔ ℓ₂)  where
  leaf : OnNode R leaf
  node : {x : A} {l r : BinaryTree A} → R x l r → OnNode R (node x l r)


Heap : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} → (R : A → A → Set ℓ₂) → BinaryTree A → Set (ℓ₁ ⊔ ℓ₂)
Heap R = AllNodes (λ x l r → OnNode (λ y _ _ → (R x y)) l
                            × OnNode (λ y _ _ → (R x y)) r)

OrderedBy : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} → (R : A → A → Set ℓ₂) → BinaryTree A → Set (ℓ₁ ⊔ ℓ₂)
OrderedBy R = AllNodes (λ x l r → All (flip R x) l × All (R x) r)


mapAllNodes : {ℓ₁ ℓ₂ ℓ₃  : Level} {A : Set ℓ₁}
            → {R : A → BinaryTree A → BinaryTree A → Set ℓ₂}
            → {S : A → BinaryTree A → BinaryTree A → Set ℓ₃}
            → {t : BinaryTree A}
            → ((a : A) → (l : BinaryTree A) → (r : BinaryTree A) → R a l r → S a l r)
            → AllNodes R t
            → AllNodes S t
mapAllNodes _ leaf = leaf
mapAllNodes {t = node x l r} f (node Rxlr allNodesRₗ allNodesRᵣ) =
  node (f x l r Rxlr) (mapAllNodes f allNodesRₗ) (mapAllNodes f allNodesRᵣ)

mapAll : {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁}
         {R : A → Set ℓ₂} {S : A → Set ℓ₃}
         {t : BinaryTree A}
       → ((a : A) → R a → S a)
       → All R t
       → All S t
mapAll f = mapAllNodes (λ x _ _ Rx → f x Rx)

mapAnyNode : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁}
             {R : A → BinaryTree A → BinaryTree A → Set ℓ₂}
             {S : A → BinaryTree A → BinaryTree A → Set ℓ₂}
           → {t : BinaryTree A}
           → ((a : A) → (l : BinaryTree A) → (r : BinaryTree A) → R a l r → S a l r)
           → AnyNode R t
           → AnyNode S t
mapAnyNode {t = node x l r} f (here Rxlr) =  here (f x l r Rxlr)
mapAnyNode {t = node x l r} f (inLeft anyRₗ) =
  inLeft (mapAnyNode f anyRₗ)
mapAnyNode {t = node x l r} f (inRight anyRᵣ) =
  inRight (mapAnyNode f anyRᵣ)


mapAny : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁}
         {R : A → Set ℓ₂} {S : A → Set ℓ₂}
       → {t : BinaryTree A}
       → ((a : A) → R a → S a)
       → Any R t
       → Any S t
mapAny f = mapAnyNode (λ x _ _ Rx → f x Rx)

member-all : {t : BinaryTree A} {a : A}
           → {P : A → Set ℓ₃}
           → All P t
           → Member a t
           → P a
member-all (node Rx all all₁) (here refl) = Rx
member-all (node _ allₗ _) (inLeft memₗ) =
  member-all allₗ memₗ
member-all (node _ _ allᵣ) (inRight memᵣ) =
  member-all allᵣ memᵣ


elem-member : (t : BinaryTree A) → All (flip Member t) t
elem-member leaf = leaf
elem-member (node x l r) =
  node (here refl)
       (mapAll (λ _ inl → inLeft inl) (elem-member l))
       (mapAll (λ _ inr → inRight inr) (elem-member r))
