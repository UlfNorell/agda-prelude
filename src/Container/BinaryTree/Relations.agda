module Container.BinaryTree.Relations where

open import Container.BinaryTree.Base
import Container.BinaryTree.Ordered as Ord

open import Prelude.Empty
open import Prelude.Equality
open import Prelude.Function
open import Prelude.Product
open import Prelude.Unit
open import Prelude.Maybe
open import Prelude.Nat

open import Prelude.Ord

open import Agda.Primitive


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

-- For membership of some part of the element (like a key in maps)
ProjMember : (proj : A → B) → B → BinaryTree A → Set _
ProjMember proj b t = Any (λ a → proj a ≡ b) t

ProjMember⇒Member : (proj : A → B) → {b : B} {t : BinaryTree A}
                  → ProjMember proj b t
                  → Σ A (λ a → Member a t × proj a ≡ b)
ProjMember⇒Member proj (here refl) = _ , (here refl , refl)
ProjMember⇒Member proj (inLeft projmem) =
  let (a , mem , eq) = ProjMember⇒Member proj projmem
  in a , inLeft mem , eq
ProjMember⇒Member proj (inRight projmem) =
  let (a , mem , eq) = ProjMember⇒Member proj projmem
  in a , inRight mem , eq

Member⇒ProjMember :
  (proj : A → B) → {a : A} {t : BinaryTree A}
  → Member a t
  → ProjMember proj (proj a) t
Member⇒ProjMember proj (here refl) = here refl
Member⇒ProjMember proj (inLeft mem) = inLeft (Member⇒ProjMember proj mem)
Member⇒ProjMember proj (inRight mem) = inRight (Member⇒ProjMember proj mem)

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
            → ({a : A} → {l : BinaryTree A} → {r : BinaryTree A}
               → R a l r → S a l r)
            → AllNodes R t
            → AllNodes S t
mapAllNodes _ leaf = leaf
mapAllNodes {t = node x l r} f (node Rxlr allNodesRₗ allNodesRᵣ) =
  node (f Rxlr) (mapAllNodes f allNodesRₗ) (mapAllNodes f allNodesRᵣ)

mapAll : {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁}
         {R : A → Set ℓ₂} {S : A → Set ℓ₃}
         {t : BinaryTree A}
       → ({a : A} → R a → S a)
       → All R t
       → All S t
mapAll f = mapAllNodes (λ Rx → f Rx)

mapAnyNode : {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁}
             {R : A → BinaryTree A → BinaryTree A → Set ℓ₂}
             {S : A → BinaryTree A → BinaryTree A → Set ℓ₃}
           → {t : BinaryTree A}
           → ({a : A} {l : BinaryTree A} {r : BinaryTree A}
              → R a l r → S a l r)
           → AnyNode R t
           → AnyNode S t
mapAnyNode {t = node x l r} f (here Rxlr) =  here (f Rxlr)
mapAnyNode {t = node x l r} f (inLeft anyRₗ) =
  inLeft (mapAnyNode f anyRₗ)
mapAnyNode {t = node x l r} f (inRight anyRᵣ) =
  inRight (mapAnyNode f anyRᵣ)

mapAny : {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁}
         {R : A → Set ℓ₂} {S : A → Set ℓ₃}
       → {t : BinaryTree A}
       → ({a : A} → R a → S a)
       → Any R t
       → Any S t
mapAny f = mapAnyNode (λ Rx → f Rx)

Member-All : {t : BinaryTree A} {a : A}
           → {P : A → Set ℓ₃}
           → Member a t
           → All P t
           → P a
Member-All (here refl) (node Rx all all₁)  = Rx
Member-All (inLeft memₗ) (node _ allₗ _) =
  Member-All memₗ allₗ
Member-All (inRight memᵣ) (node _ _ allᵣ) =
  Member-All memᵣ allᵣ

ProjMember-All :
  ∀ {ℓ₃}
  → {P : B → Set ℓ₃}
  → (proj : A → B)
  → {t : BinaryTree A} {b : B}
  → ProjMember proj b t
  → All (P ∘ proj) t
  → P b
ProjMember-All proj (here refl) (node Px _ _) = Px
ProjMember-All proj (inLeft projmem) (node _ all _) =
  ProjMember-All proj projmem all
ProjMember-All proj (inRight projmem) (node _ _ all) =
  ProjMember-All proj projmem all

all-self-Member : (t : BinaryTree A) → All (flip Member t) t
all-self-Member leaf = leaf
all-self-Member (node x l r) =
  node (here refl)
       (mapAll (λ inl → inLeft inl) (all-self-Member l))
       (mapAll (λ inr → inRight inr) (all-self-Member r))

all-self-ProjMember : (proj : A → B) → (t : BinaryTree A) → All (λ a → ProjMember proj (proj a) t) t
all-self-ProjMember proj t = mapAll (λ mem → Member⇒ProjMember proj mem) (all-self-Member t)


All¬⇒¬Any :
  ∀ {ℓ₃}
  → {P : A → Set ℓ₃}
  → {t : BinaryTree A}
  → All (λ a → ¬ (P a)) t
  → ¬ (Any P t)
All¬⇒¬Any leaf = λ ()
All¬⇒¬Any (node x all all₁) (here x₁) = x x₁
All¬⇒¬Any (node x all all₁) (inLeft any) = All¬⇒¬Any all any
All¬⇒¬Any (node x all all₁) (inRight any) = All¬⇒¬Any all₁ any

¬Any⇒All¬ :
  ∀ {ℓ₃}
  → {P : A → Set ℓ₃}
  → {t : BinaryTree A}
  → ¬ (Any P t)
  → All (λ a → ¬ (P a)) t
¬Any⇒All¬ {t = leaf} ¬any = leaf
¬Any⇒All¬ {t = node x t t₁} ¬any = node (λ z → ¬any (here z)) (¬Any⇒All¬ (λ z → ¬any (inLeft z))) (¬Any⇒All¬ (λ z → ¬any (inRight z)))

OrderedBy-Member-Injective :
  {{_ : Ord/Laws B}}
  (proj : A → B)
  → (a : A)
  → (t : BinaryTree A)
  → (OrderedBy (λ p₁ p₂ → proj p₁ < proj p₂) t)
  → Member a t
  → (b : A)
  → Member b t
  → proj a ≡ proj b
  → a ≡ b
OrderedBy-Member-Injective proj a leaf leaf () b mem[b] pa≡pb
OrderedBy-Member-Injective proj a (node x l r) (node (all[l]<x , all[r]>x) ord[l] ord[r]) (here x≡a) b (here x≡b) pa≡pb =
  trans (sym x≡a) x≡b
OrderedBy-Member-Injective proj a (node x l r) (node (all[l]<x , all[r]>x) ord[l] ord[r]) (here x≡a) b (inLeft mem[b]) pa≡pb =
  ⊥-elim (less-antirefl (transport (proj b <_) pa≡pb (transport (λ z → proj b < proj z) x≡a (Member-All mem[b] all[l]<x))))
OrderedBy-Member-Injective proj a (node x l r) (node (all[l]<x , all[r]>x) ord[l] ord[r]) (here x≡a) b (inRight mem[b]) pa≡pb =
  ⊥-elim (less-antirefl ((transport (_< proj b) pa≡pb (transport (λ z → proj z < proj b) x≡a (Member-All mem[b] all[r]>x))) ) )
OrderedBy-Member-Injective proj a (node x l r) (node (all[l]<x , all[r]>x) ord[l] ord[r]) (inLeft mem[a]) b (here x≡b) pa≡pb =
  ⊥-elim (less-antirefl (transport (_< proj b) pa≡pb (transport (λ z → proj a < proj z) x≡b (Member-All mem[a] all[l]<x))))
OrderedBy-Member-Injective proj a (node x l r) (node (all[l]<x , all[r]>x) ord[l] ord[r]) (inLeft mem[a]) b (inLeft mem[b]) pa≡pb =
  OrderedBy-Member-Injective proj a l ord[l] mem[a] b mem[b] pa≡pb
OrderedBy-Member-Injective proj a (node x l r) (node (all[l]<x , all[r]>x) ord[l] ord[r]) (inLeft mem[a]) b (inRight mem[b]) pa≡pb =
  ⊥-elim (less-antirefl (transport (_< proj b) pa≡pb (less-trans (Member-All mem[a] all[l]<x) (Member-All mem[b] all[r]>x))))
OrderedBy-Member-Injective proj a (node x l r) (node (all[l]<x , all[r]>x) ord[l] ord[r]) (inRight mem[a]) b (here x≡b) pa≡pb =
  ⊥-elim (less-antirefl (transport (proj b <_) pa≡pb (transport (λ z → proj z < proj a) x≡b (Member-All mem[a] all[r]>x))))
OrderedBy-Member-Injective proj a (node x l r) (node (all[l]<x , all[r]>x) ord[l] ord[r]) (inRight mem[a]) b (inLeft mem[b]) pa≡pb =
  ⊥-elim (less-antirefl (transport (proj b <_) pa≡pb ( (less-trans (Member-All mem[b] all[l]<x) (Member-All mem[a] all[r]>x)))))
OrderedBy-Member-Injective proj a (node x l r) (node (all[l]<x , all[r]>x) ord[l] ord[r]) (inRight mem[a]) b (inRight mem[b]) pa≡pb =
  OrderedBy-Member-Injective proj a r ord[r] mem[a] b mem[b] pa≡pb
