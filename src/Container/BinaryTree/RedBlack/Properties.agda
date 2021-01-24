module Container.BinaryTree.RedBlack.Properties where

open import Container.BinaryTree.RedBlack
open Insert
open Karhs

open import Container.BinaryTree.Base
import Container.BinaryTree.Ordered as Ord
open import Container.BinaryTree.Ordered.Properties
open import Container.BinaryTree.Relations

open import Agda.Primitive
open import Prelude.Product
open import Prelude.Function
open import Prelude.Functor
open import Prelude.Equality
open import Prelude.Ord
open import Prelude.Ord.Properties
open import Prelude.Empty
open import Prelude.Maybe
open import Prelude.Sum
open import Prelude.Unit

open import Prelude.Variables

private
  -- Private synonym for bevity
  RB : ∀ {ℓ} → Set ℓ → Set ℓ
  RB = RedBlackTree

-- Special version of member for red-black trees

RBMember : A → RedBlackTree A → Set _
RBMember a t = ProjMember snd a t


RBProjMember : (proj : A → B) → B → RedBlackTree A → Set _
RBProjMember proj k t = ProjMember (proj ∘ snd) k t

RBProjMember⇒RBMember :
  {proj : A → B}
  → {b : B} → {t : RedBlackTree A}
  → RBProjMember proj b t
  → Σ A (λ a → proj a ≡ b × RBMember a t)
RBProjMember⇒RBMember {t = node (_ , x) _ _} (here refl) =
  x , (refl , here refl)
RBProjMember⇒RBMember (inLeft pmem)
  with RBProjMember⇒RBMember pmem
... | a , refl , snd₁ = (a , refl , inLeft snd₁ )
RBProjMember⇒RBMember (inRight pmem)
  with RBProjMember⇒RBMember pmem
... | a , refl , snd₁ = (a , refl , inRight snd₁ )

Member⇒RBMember :
    {c : Color} {a : A} {t : RB A}
  → Member (c , a) t → RBMember a t
Member⇒RBMember mem = Member⇒ProjMember snd mem

RBMember⇒Member : {a : A} {t : RedBlackTree A} → RBMember a t → Σ Color (λ c → Member (c , a) t)
RBMember⇒Member projmem
  with ProjMember⇒Member snd projmem
...| (color , a') , mem , a'≡a rewrite a'≡a = color , mem

elem-RBMember : (t : RedBlackTree A) → All (λ a → RBMember (snd a) t) t
elem-RBMember t = all-self-ProjMember snd t

RBMember-All : {a : A} → {t : RB A} → {P : A → Set ℓ₃} → All (P ∘ snd) t → RBMember a t → P a
RBMember-All all rbmem = ProjMember-All snd rbmem all

lookupBy-¬RBProjMember :
  (proj : A → B)
  → {{_ : Ord B}}
  → {b : B} → {t : RedBlackTree A}
  → ¬ RBProjMember proj b t
  → lookupBy proj b t ≡ nothing
lookupBy-¬RBProjMember proj {b = b} {t} ¬mem
  rewrite binarySearchBy-¬ProjMember (proj ∘ snd) b t ¬mem = refl

lookupBy-RBMember :
  {{_ : Ord/Laws B}}
  → (proj : A → B)
  → (a : A)
  → (t : RedBlackTree A)
  → RBMember a t
  → OrderedBy (λ a b → proj (snd a) < proj (snd b)) t
  → lookupBy proj (proj a) t ≡ just a
lookupBy-RBMember proj a t@(node _ _ _) mem ord[t]
  with binarySearchBy-ProjProjMember snd proj a t mem ord[t]
... | (_ , .a) , bs≡ , refl rewrite bs≡ = refl

lookupBy-cases :
    {{_ : Ord/Laws B}}
  → (proj : A → B)
  → (k : B)
  → {t : RedBlackTree A}
  → OrderedBy (λ a b → proj (snd a) < proj (snd b)) t
  → Either (Σ A (λ a → lookupBy proj k t ≡ just a
                     × RBMember a t
                     × proj a ≡ k))
           (lookupBy proj k t ≡ nothing
           × ¬ RBProjMember proj k t)
lookupBy-cases proj k {t = t} ord[t]
  with binarySearch-cases (proj ∘ snd) k t ord[t]
... | left ((_ , snd₁) , fst₂ , fst₃ , snd₂) rewrite fst₂ =
  left (snd₁ , (refl , Member⇒ProjMember snd  snd₂ , fst₃))
... | right (fst₁ , snd₁) rewrite fst₁ = right (refl , snd₁)

module _ {l : Level} {A : Set l} where

  MatchTuple : Set l
  MatchTuple = (A × A × RedBlackTree A × RedBlackTree A × RedBlackTree A)
  -- Used to simplify proofs, since there really are just three cases
  leftBalance-effect :
    (color : Color)
    → (z : A) → (l : RedBlackTree A) → (r : RedBlackTree A)
    → Either (leftBalance color z l r ≡ node (color , z) l r)
             (Σ MatchTuple (λ { (x , y , a , b , c) →
                 Either (l ≡ (node (red , y) (node (red , x) a b) c))
                        (l ≡ (node (red , x) a (node (red , y) b c)))
                 × leftBalance color z l r ≡ node (red , y) (node (black , x) a b) (node (black , z) c r)
               }))
  leftBalance-effect red z l r = left refl
  leftBalance-effect black z leaf r = left refl
  leftBalance-effect black z (node (red , snd₁) leaf leaf) r = left refl
  leftBalance-effect black z (node (red , x) a@leaf (node (red , y) b c)) leaf =
    right ((x , y , a , b , c) , right refl , refl)
  leftBalance-effect black z (node (red , x) a@leaf (node (red , y) b c)) (node _ _ _) =
    right ((x , y , a , b , c) , right refl , refl)
  leftBalance-effect black z (node (red , _) leaf (node (black , _) _ _)) r = left refl
  leftBalance-effect black z (node (red , x) (node (red , y) a b) c) r =
    right ((y , x , a , b , c) , left refl , refl)
  leftBalance-effect black z (node (red , x) a@(node (black , _) _ _) leaf) r = left refl
  leftBalance-effect black z (node (red , x) a@(node (black , _) _ _) (node (black , y) b c)) r =
    left refl
  leftBalance-effect black z (node (red , x) a@(node (black , _) _ _) (node (red , y) b c)) r =
    right ((x , y , a , b , c) , (right refl , refl))
  leftBalance-effect black z (node (black , snd₁) l l₁) r = left refl

  rightBalance-effect :
    (color : Color)
    → (x : A) → (a : RedBlackTree A) → (r : RedBlackTree A)
    → Either (rightBalance color x a r ≡ node (color , x) a r)
             (Σ MatchTuple (λ { (y , z , b , c , d) →
                 Either (r ≡ (node (red , z) (node (red , y) b c) d))
                        (r ≡ (node (red , y) b (node (red , z) c d)))
                 × rightBalance color x a r ≡ node (red , y) (node (black , x) a b) (node (black , z) c d)
               }))
  rightBalance-effect red x l r = left refl
  rightBalance-effect black x l leaf = left refl
  rightBalance-effect black x a (node (red , y) leaf leaf) = left refl
  rightBalance-effect black x a (node (red , y) b@leaf (node (red , z) c d)) =
    right ((y , z , b , c , d) , right refl , refl)
  rightBalance-effect black x a (node (red , y) leaf (node (black , z) r₁ r₂)) = left refl
  rightBalance-effect black x a (node (red , y) b@(node (black , _) _ _) leaf) = left refl
  rightBalance-effect black x a (node (red , y) b@(node (black , _) _ _) (node (red , z) c d)) =
    right ((y , z , b , c , d) , right refl , refl)
  rightBalance-effect black x a (node (red , y) b@(node (black , _) _ _) (node (black , z) c d)) = left refl
  rightBalance-effect black x a (node (red , y) (node (red , z) b c) d) =
    right ((z , y , b , c , d) , left refl , refl)
  rightBalance-effect black x a (node (black , y) r r₁) = left refl

leftBalance-ordered :
  {{_ : Ord/Laws B}}
  → {proj : A → B}
  → (color : Color)
  → (x : A) → (l : RedBlackTree A) → (r : RedBlackTree A)
  → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) l
  → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) r
  → All (λ p → proj (snd p)  < proj x) l → All (λ p → proj x < proj (snd p)) r
  → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) (leftBalance color x l r)
leftBalance-ordered color z l r ord[l] ord[r] all[l]<z all[r]>z
  with leftBalance-effect color z l r
... | left x₁ rewrite x₁ = node (all[l]<z , all[r]>z) ord[l] ord[r]
... | right ((x , y , a , b , c) , left refl , leftBalance≡) rewrite leftBalance≡ =
  case (ord[l] , all[l]<z) of
    λ { (node (node x<y all[a]<y all[b]>y , all[c]>y) (node (all[a]<x , all[b]>x) ord[lll] ord[llr]) ord[lr]
         , node y<z (node x<z all[a]<z all[b]<z) all[c]<z) →
           node ((node x<y all[a]<y all[b]>y)
                , (node y<z all[c]>y (mapAll (λ z<a → less-trans y<z z<a) all[r]>z)))
                (node (all[a]<x , all[b]>x) ord[lll] ord[llr])
                (node (all[c]<z , all[r]>z) ord[lr] ord[r])
      }
... | right ((x , y , a , b , c) , right refl , leftBalance≡) rewrite leftBalance≡ =
  case (ord[l] , all[l]<z) of
    λ { (node (all[a]<x , node x<y all[b]>x all[c]>x) ord[a] (node (all[b]<y , all[c]>y) ord[b] ord[c])
        , node x<z all[l]<z (node y<z all[b]<z all[c]<z)) →
          node ((node x<y (mapAll (λ a<x → less-trans a<x x<y) all[a]<x) all[b]<y)
               , (node y<z all[c]>y (mapAll (λ z>a → less-trans y<z z>a) all[r]>z)))
               (node (all[a]<x , all[b]>x) ord[a] ord[b])
               (node (all[c]<z , all[r]>z) ord[c] ord[r])
      }

leftBalance-All :
  ∀ {ℓ₂}
  → {P : A → Set ℓ₂}
  → (color : Color) → (x : A) → (l : RedBlackTree A) → (r : RedBlackTree A)
  → P x
  → All (P ∘ snd) l → All (P ∘ snd) r
  → All (P ∘ snd) (leftBalance color x l r)
leftBalance-All color x l r Px allP[l] allP[r]
  with leftBalance-effect color x l r
...| left leftBalance≡ rewrite leftBalance≡ = node Px allP[l] allP[r]
...| right ((z , y , a , b , c) , left refl , leftBalance≡) rewrite leftBalance≡ =
  case allP[l] of
    λ { (node Py (node Pz allP[a] allP[b]) allP[c]) → node Py (node Pz allP[a] allP[b]) (node Px allP[c] allP[r]) }
...| right ((y , z , a , b , c) , right refl , leftBalance≡) rewrite leftBalance≡ =
  case allP[l] of
    λ { (node Py allP[a] (node Pz allP[b] allP[c])) → node Pz (node Py allP[a] allP[b]) (node Px allP[c] allP[r]) }

leftBalance-Any :
  ∀ {ℓ₂}
  → {P : A → Set ℓ₂}
  → (color : Color) → (x : A) → (l : RedBlackTree A) → (r : RedBlackTree A)
  → Either (P x) (Either (Any (P ∘ snd) l) (Any (P ∘ snd) r))
  → Any (P ∘ snd) (leftBalance color x l r)
leftBalance-Any color x l r anyP
  with leftBalance-effect color x l r
...| left leftBalance≡ rewrite leftBalance≡ =
  case anyP of
    λ { (left Px) → here Px
      ; (right (left anyPleft)) → inLeft anyPleft
      ; (right (right anyPright)) → inRight anyPright }
...| right ((z , y , a , b , c) , left refl , leftBalance≡) rewrite leftBalance≡ =
  case anyP of
    λ { (left Px) → inRight (here Px)
      ; (right (left (here Py))) → here Py
      ; (right (left (inLeft (here Pz)))) → inLeft (here Pz)
      ; (right (left (inLeft (inLeft anyP[a])))) → inLeft (inLeft anyP[a])
      ; (right (left (inLeft (inRight anyP[b])))) → inLeft (inRight anyP[b])
      ; (right (left (inRight anyP[c]))) → inRight (inLeft anyP[c])
      ; (right (right anyP[r])) → inRight (inRight anyP[r])
      }
...| right ((y , z , a , b , c) , right refl , leftBalance≡) rewrite leftBalance≡ =
  case anyP of
    λ { (left Px) → inRight (here Px)
      ; (right (left (here Py))) → inLeft (here Py)
      ; (right (left (inLeft (here Pz)))) → inLeft (inLeft (here Pz))
      ; (right (left (inLeft (inLeft anyP[a])))) → inLeft (inLeft (inLeft anyP[a]))
      ; (right (left (inLeft (inRight anyP[b])))) → inLeft (inLeft (inRight anyP[b]))
      ; (right (left (inRight (here Pz)))) → here Pz
      ; (right (left (inRight (inLeft anyP[b])))) → inLeft (inRight anyP[b])
      ; (right (left (inRight (inRight anyP[c])))) → inRight (inLeft anyP[c])
      ; (right (right anyP[r])) → inRight (inRight anyP[r])
      }

rightBalance-ordered :
  {{_ : Ord/Laws B}}
  → {proj : A → B}
  → (color : Color)
  → (x : A) → (l : RedBlackTree A) → (r : RedBlackTree A)
  → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) l
  → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) r
  → All (λ p → proj (snd p)  < proj x) l → All (λ p → proj x < proj (snd p)) r
  → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) (rightBalance color x l r)
rightBalance-ordered color x l r ord[l] ord[r] all[l]<x all[r]>x
  with rightBalance-effect color x l r
... | left rightBalance≡ rewrite rightBalance≡ = node (all[l]<x , all[r]>x) ord[l] ord[r]
... | right ((z , y , a , b , c) , left refl , rightBalance≡) rewrite rightBalance≡ =
  case (ord[r] , all[r]>x) of
    λ { (node ((node z<y all[a]<y all[b]<y) , all[c]>y) (node (all[a]<z , all[b]>z) ord[a] ord[b]) ord[c]
        , node x<y (node x<z all[a]>x all[b]>x) all[c]>x) →
          node ((node x<z (mapAll (λ a<x → less-trans a<x x<z) all[l]<x) all[a]<z)
               , (node z<y all[b]>z (mapAll (λ a>y → less-trans z<y a>y ) all[c]>y)))
               (node (all[l]<x , all[a]>x) ord[l] ord[a])
               (node (all[b]<y , all[c]>y) ord[b] ord[c])
    }
... | right ((y , z , a , b , c) , right refl , rightBalance≡) rewrite rightBalance≡ =
   case (ord[r] , all[r]>x) of
     λ { (node (all[a]<y , node y<z all[b]>y all[c]>y) ord[a] (node (all[b]<z , all[c]>z) ord[b] ord[c])
         , node x<y all[r]>x (node x<z all[b]>x all[c]>x)) →
           node ((node x<y (mapAll (λ a<x → less-trans a<x x<y) all[l]<x) all[a]<y)
                , (node y<z all[b]>y all[c]>y))
                (node (all[l]<x , all[r]>x) ord[l] ord[a])
                (node (all[b]<z , all[c]>z) ord[b] ord[c])
        }

rightBalance-All :
  ∀ {ℓ₂}
  → {P : A → Set ℓ₂}
  → (color : Color) → (x : A) → (l : RedBlackTree A) → (r : RedBlackTree A)
  → P x
  → All (P ∘ snd) l → All (P ∘ snd) r
  → All (P ∘ snd) (rightBalance color x l r)
rightBalance-All color x l r Px allP[l] allP[r]
  with rightBalance-effect color x l r
...| left rightBalance≡ rewrite rightBalance≡ = node Px allP[l] allP[r]
...| right ((z , y , a , b , c) , left refl , rightBalance≡) rewrite rightBalance≡ =
  case allP[r] of
    λ { (node Py (node Pz allP[a] allP[b]) allP[c]) → node Pz (node Px allP[l] allP[a]) (node Py allP[b] allP[c]) }
...| right ((y , z , a , b , c) , right refl , rightBalance≡) rewrite rightBalance≡ =
  case allP[r] of
    λ { (node Py allP[a] (node Pz allP[b] allP[c])) → node Py (node Px allP[l] allP[a]) (node Pz allP[b] allP[c]) }


rightBalance-Any :
  ∀ {ℓ₂}
  → {P : A → Set ℓ₂}
  → (color : Color) → (x : A) → (l : RedBlackTree A) → (r : RedBlackTree A)
  → Either (P x) (Either (Any (P ∘ snd) l) (Any (P ∘ snd) r))
  → Any (P ∘ snd) (rightBalance color x l r)
rightBalance-Any color x l r anyP
  with rightBalance-effect color x l r
...| left rightBalance≡ rewrite rightBalance≡ =
  case anyP of
    λ { (left Px) → here Px
    ; (right (left anyP[l])) → inLeft anyP[l]
    ; (right (right anyP[r])) → inRight anyP[r]}
...| right ((z , y , a , b , c) , left refl , rightBalance≡) rewrite rightBalance≡ =
  case anyP of
    λ { (left Px) → inLeft (here Px)
    ; (right (left anyP[l])) → inLeft (inLeft anyP[l])
    ; (right (right (here Py))) → inRight (here Py)
    ; (right (right (inLeft (here Pz)))) → here Pz
    ; (right (right (inLeft (inLeft anyP[a])))) → inLeft (inRight anyP[a])
    ; (right (right (inLeft (inRight anyP[b])))) → inRight (inLeft anyP[b])
    ; (right (right (inRight anyP[c]))) → inRight (inRight anyP[c])
    }
...| right ((y , z , a , b , c) , right refl , rightBalance≡) rewrite rightBalance≡ =
  case anyP of
    λ { (left Px) → inLeft (here Px)
      ; (right (left anyP[l])) → inLeft (inLeft anyP[l])
      ; (right (right (here Py))) → here Py
      ; (right (right (inLeft anyP[a]))) → inLeft (inRight anyP[a])
      ; (right (right (inRight (here Pz)))) → inRight (here Pz)
      ; (right (right (inRight (inLeft anyP[b])))) → inRight (inLeft anyP[b])
      ; (right (right (inRight (inRight anyP[c])))) → inRight (inRight anyP[c])
      }


insertInner-All :
  ∀ {ℓ₂}
  → {P : A → Set ℓ₂}
  → {{_ : Ord B}}
  → (proj : A → B)
  → (x : A) → (t : RedBlackTree A)
  → P x
  → All (P ∘ snd) t
  → All (P ∘ snd) (insertInner proj (proj x) x t)
insertInner-All proj x .leaf Px leaf = node Px leaf leaf
insertInner-All proj x (node (color , a') l r) Px (node Pa' allP[l] allP[r])
  with compare (proj x) (proj a')
... | less lt =
  leftBalance-All
    color a'
    (insertInner proj (proj x) x l)
    r Pa'
    (insertInner-All proj x l Px allP[l])
    allP[r]
... | equal eq = node Px allP[l] allP[r]
... | greater gt =
  rightBalance-All
    color a' l
    (insertInner proj (proj x) x r)
    Pa'
    allP[l]
    (insertInner-All proj x r Px allP[r])

insertInner-ordered :
  {{_ : Ord/Laws B}}
  → (proj : A → B)
  → (x : A)
  → (t : RedBlackTree A)
  → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) t
  → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) (insertInner proj (proj x) x t)
insertInner-ordered _ x leaf leaf =
  node (leaf , leaf) leaf leaf
insertInner-ordered
  proj x
  (node (color , y) l r)
  ord[t]@(node (all[l]<y , all[r]>y) ord[l] ord[r])
  with compare (proj x) (proj y)
...| equal x≡b =
  node (transport (λ z → All (λ x → proj (snd x) < z) l) (sym x≡b) all[l]<y
       , transport (λ z → All (λ x → z < proj (snd x)) r) (sym x≡b) all[r]>y) ord[l] ord[r]
...| greater y<x with insertInner proj (proj x) x r
                    | insertInner-ordered proj x r ord[r]
                    | insertInner-All proj x r y<x all[r]>y
... | leaf | leaf | _ = rightBalance-ordered color y l leaf ord[l] leaf all[l]<y leaf
... | r'@(node _ _ _) | ord[r']@(node _ _ _) | allP[insertInner] =
  rightBalance-ordered
    color y l r'
    ord[l] ord[r']
    all[l]<y allP[insertInner]
insertInner-ordered proj x (node (color , y) l r) ord[t]@(node (all[l]<y , all[r]>y) ord[l] ord[r])
  | less x<y with insertInner proj (proj x) x l
                | insertInner-ordered proj x l ord[l]
                | insertInner-All proj x l x<y all[l]<y
... | leaf | leaf | _ =
  leftBalance-ordered color y leaf r leaf ord[r] leaf all[r]>y
... | l'@(node _ _ _) | ord[l']@(node _ _ _) | allP[insertInner] =
  leftBalance-ordered
    color y l' r
    ord[l'] ord[r]
    allP[insertInner] all[r]>y

insertBy-ordered :
  {{_ : Ord/Laws B}}
  → (proj : A → B)
  → (x : A)
  → (t : RB A)
  → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) t
  → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) (insertBy proj x t)
insertBy-ordered proj x t ord[t]
  with insertInner proj (proj x) x t | insertInner-ordered proj x t ord[t]
... | leaf | leaf = leaf
... | node x₁ foo foo₁ | node x₂ bar bar₁ = node x₂ bar bar₁

insertInner-Member :
    {{_ : Ord B}}
  → (proj : A → B)
  → (x : A)
  → (t : RedBlackTree A)
  → RBMember x (insertInner proj (proj x) x t)
insertInner-Member proj x leaf = here refl
insertInner-Member proj x (node (c , y) l r)
  with compare (proj x) (proj y)
... | less lt = leftBalance-Any c y _ r (right (left (insertInner-Member proj x l)))
... | equal eq = here refl
... | greater gt = rightBalance-Any c y l _ (right (right (insertInner-Member proj x r)))


insertBy-Member :
    {{_ : Ord B}}
  → (proj : A → B)
  → (x : A)
  → (t : RedBlackTree A)
  → RBMember x (insertBy proj x t)
insertBy-Member proj x t with insertInner proj (proj x) x t | insertInner-Member proj x t
... | leaf | ()
... | node x₁ q q₁ | here x₂ = here x₂
... | node x₁ q q₁ | inLeft w = inLeft w
... | node x₁ q q₁ | inRight w = inRight w

insertInner-keeps-Member :
    {{_ : Ord B}}
  → (proj : A → B)
  → (x : A)
  → (x' : A)
  → (t : RedBlackTree A)
  → (proj x ≢ proj x')
  → RBMember x' t
  → RBMember x' (insertInner proj (proj x) x t)
insertInner-keeps-Member proj x x' (node (c , y) l r) p[x]≢p[x'] (here x'≡y)
  with compare (proj x) (proj y)
... | less lt = leftBalance-Any c y _ r (left x'≡y)
... | equal eq rewrite eq rewrite x'≡y = ⊥-elim (p[x]≢p[x'] refl)
... | greater gt = rightBalance-Any c y l _ (left x'≡y)
insertInner-keeps-Member proj x x' (node (c , y) l r) p[x]≢p[x'] (inLeft x'∈l)
  with compare (proj x) (proj y)
... | less lt = leftBalance-Any c y _ r (right (left (insertInner-keeps-Member proj x x' l p[x]≢p[x'] x'∈l)))
... | equal eq = inLeft x'∈l
... | greater gt = rightBalance-Any c y l _ (right (left x'∈l))
insertInner-keeps-Member proj x x' (node (c , y) l r) p[x]≢p[x'] (inRight x'∈r)
  with compare (proj x) (proj y)
... | less lt = leftBalance-Any c y _ r (right (right x'∈r))
... | equal eq = inRight x'∈r
... | greater gt = rightBalance-Any c y l _ (right (right (insertInner-keeps-Member proj x x' r p[x]≢p[x'] x'∈r)))


insertBy-keeps-Member :
    {{_ : Ord B}}
  → (proj : A → B)
  → (x : A)
  → (x' : A)
  → (t : RedBlackTree A)
  → (proj x ≢ proj x')
  → RBMember x' t
  → RBMember x' (insertBy proj x t)
insertBy-keeps-Member proj x x' t p[x]≢p[x'] x'∈t
   with insertInner proj (proj x) x t | insertInner-keeps-Member proj x x' t p[x]≢p[x'] x'∈t
... | leaf | ()
... | node _ _ _ | here x₂ = here x₂
... | node _ _ _ | inLeft w = inLeft w
... | node _ _ _ | inRight w = inRight w

insertInner-keeps-¬Member :
    {{_ : Ord B}}
  → (proj : A → B)
  → (x : A)
  → (x' : A)
  → (t : RedBlackTree A)
  → (proj x ≢ proj x')
  → RBMember x' t
  → RBMember x' (insertInner proj (proj x) x t)
insertInner-keeps-¬Member proj x x' (node (c , y) l r) p[x]≢p[x'] (here x'≡y)
  with compare (proj x) (proj y)
... | less lt = leftBalance-Any c y _ r (left x'≡y)
... | equal eq rewrite eq rewrite x'≡y = ⊥-elim (p[x]≢p[x'] refl)
... | greater gt = rightBalance-Any c y l _ (left x'≡y)
-- insertInner-keeps-¬Member proj x x' (node (c , y) l r) p[x]≢p[x'] (inLeft x'∈l)
--   with compare (proj x) (proj y)
-- ... | less lt = leftBalance-Any c y _ r (right (left (insertInner-keeps-Member proj x x' l p[x]≢p[x'] x'∈l)))
-- ... | equal eq = inLeft x'∈l
-- ... | greater gt = rightBalance-Any c y l _ (right (left x'∈l))
-- insertInner-keeps-¬Member proj x x' (node (c , y) l r) p[x]≢p[x'] (inRight x'∈r)
--   with compare (proj x) (proj y)
-- ... | less lt = leftBalance-Any c y _ r (right (right x'∈r))
-- ... | equal eq = inRight x'∈r
-- ... | greater gt = rightBalance-Any c y l _ (right (right (insertInner-keeps-Member proj x x' r p[x]≢p[x'] x'∈r)))


balance-cases :
    (q : A) → (l : RedBlackTree A) → (r : RedBlackTree A)
  → Either (balance l q r ≡ node (black , q) l r)
       (Either (Σ (MatchTuple × RedBlackTree A) (λ { ((x , y , a , b , c) , d) →
                 l ≡ node (red , x) a b
                 × r ≡ node (red , y) c d
                 × balance l q r ≡ node (red , q) (node (black , x) a b) (node (black , y) c d)
                 }
                 ))
           (Either
             (Σ MatchTuple (λ { (x , y , a , b , c) →
               (Either (l ≡ node (red , y) (node (red , x) a b) c)
                       (l ≡ node (red , x) a (node (red , y) b c)))
               × balance l q r ≡ node (red , y) (node (black , x) a b) (node (black , q) c r)
             }))
            (Σ MatchTuple (λ { (y , z , b , c , d) →
               (Either (r ≡ (node (red , y) b (node (red , z) c d)))
                       (r ≡ (node (red , z) (node (red , y) b c) d)))
               × balance l q r ≡ node (red , y) (node (black , q) l b) (node (black , z) c d)
                         }))
           ))
balance-cases z leaf leaf = left refl
balance-cases z leaf (node (red , snd₁) leaf leaf) = left refl
balance-cases x a@leaf (node (red , y) b@leaf (node (red , z) c d)) =
  right (right (right ( (y , z , leaf , c , d) , left refl , refl)))
balance-cases x a@leaf (node (red , y) b@leaf (node (black , z) c d)) =
  left refl
balance-cases x a@leaf (node (red , y) (node (red , z) b c) d@leaf) =
  right (right (right ( (z , y , b , c , d) , right refl , refl)))
balance-cases x a@leaf (node (red , z) b@(node (red , _) _ _) (node (red , y) c d)) =
  right (right (right ( (z , y , b , c , d) , left refl , refl)))
balance-cases x a@leaf (node (red , y) (node (red , z) b c) d@(node (black , _) _ _)) =
  right (right (right ( (z , y , b , c , d) , right refl , refl)))
balance-cases x a@leaf (node (red , y) b@(node (black , _) _ _) leaf) =
  left refl
balance-cases x a@leaf (node (red , y) b@(node (black , _) _ _) (node (red , z) c d)) =
  right (right (right ( (y , z , b , c , d) , left refl , refl)))
balance-cases x a@leaf (node (red , y) b@(node (black , _) _ _) (node (black , z) c d)) =
  left refl
balance-cases x leaf (node (black , y) _ _) = left refl
balance-cases z (node (red , y) leaf leaf) leaf = left refl
balance-cases z (node (red , x) a@leaf (node (red , y) b c)) leaf =
  right (right (left ((x , y , a , b , c) , right refl , refl)))
balance-cases z (node (red , x) leaf (node (black , y) _ _)) leaf = left refl
balance-cases z (node (red , x) (node (red , y) a b) c@leaf) leaf =
  right (right (left ((y , x , a , b , c) , left refl , refl)))
balance-cases z (node (red , x) (node (black , y) _ _) leaf) leaf = left refl
balance-cases z (node (red , x) (node (red , y) a b) c@(node (red , _) _ _)) leaf =
  right (right (left ((y , x , a , b , c) , left refl , refl)))
balance-cases z (node (red , x) (node (red , y) a b) c@(node (black , _) _ _)) leaf =
  right (right (left ((y , x , a , b , c) , left refl , refl)))
balance-cases z (node (red , x) a@(node (black , _) _ _) (node (red , y) b c)) leaf =
  right (right (left ((x , y , a , b , c) , right refl , refl)))
balance-cases z (node (red , x) (node (black , _) _ _) (node (black , _) _ _)) leaf =
  left refl
balance-cases z (node (black , x) l l₁) leaf = left refl
balance-cases z (node (red , x) leaf leaf) (node (black , snd₁) r r₁) = left refl
balance-cases z (node (red , _) _ _) (node (red , _) _ _) =
  right (left (_ , refl , refl , refl))
balance-cases z (node (red , x) a@leaf (node (red , y) b c)) r@(node (black , _) _ _) =
  right (right (left (_ , right refl , refl)))
balance-cases z (node (red , x) leaf (node (black , snd₂) l₁ l₂)) (node (black , snd₁) r r₁) = left refl
balance-cases z (node (red , x) (node (red , snd₁) l l₁) leaf) (node (black , _) _ _) =
  right (right (left (_ , left refl , refl)))
balance-cases z (node (red , x) (node (black , snd₁) l l₁) leaf) (node (black , snd₂) r r₁) = left refl
balance-cases z (node (red , x) (node (red , snd₁) l l₁) (node (red , snd₃) l₂ l₃)) (node (black , snd₂) r r₁) =
  right (right (left (_ , left refl , refl)))
balance-cases z (node (red , x) (node (red , snd₁) l l₁) (node (black , snd₃) l₂ l₃)) (node (black , snd₂) r r₁) =
  right (right (left (_ , left refl , refl)))
balance-cases z (node (red , x) (node (black , snd₁) l l₁) (node (red , snd₃) l₂ l₃)) (node (black , snd₂) r r₁) =
  right (right (left (_ , right refl , refl)))
balance-cases z (node (red , x) (node (black , snd₁) l l₁) (node (black , snd₃) l₂ l₃)) (node (black , snd₂) r r₁) = left refl
balance-cases z (node (black , x) l l₁) (node (red , snd₁) leaf leaf) = left refl
balance-cases z (node (black , x) l l₁) (node (red , snd₁) leaf (node (red , snd₂) r₁ r₂)) =
    right (right (right (_ , left refl , refl)))
balance-cases z (node (black , x) l l₁) (node (red , snd₁) leaf (node (black , snd₂) r₁ r₂)) = left refl
balance-cases z (node (black , x) l l₁) (node (red , snd₁) (node (red , snd₂) r r₁) leaf) =
    right (right (right (_ , right refl , refl)))
balance-cases z (node (black , x) l l₁) (node (red , snd₁) (node (black , snd₂) r r₁) leaf) = left refl
balance-cases z (node (black , x) l l₁) (node (red , snd₁) (node (red , snd₂) r r₁) (node (red , snd₃) r₂ r₃)) =
    right (right (right (_ , left refl , refl)))
balance-cases z (node (black , x) l l₁) (node (red , snd₁) (node (red , snd₂) r r₁) (node (black , snd₃) r₂ r₃)) =
    right (right (right (_ , right refl , refl)))
balance-cases z (node (black , x) l l₁) (node (red , snd₁) (node (black , snd₂) r r₁) (node (red , snd₃) r₂ r₃)) =
    right (right (right (_ , left refl , refl)))
balance-cases z (node (black , x) l l₁) (node (red , snd₁) (node (black , snd₂) r r₁) (node (black , snd₃) r₂ r₃)) =
    left refl
balance-cases z (node (black , x) l l₁) (node (black , snd₁) r r₁) = left refl


-- Proofs here are basically copy-pastas of the left and right balance variants above. The names doesn't make sense
balance-ordered :
  {{_ : Ord/Laws B}}
  → {proj : A → B}
  → (x : A) → (l : RedBlackTree A) → (r : RedBlackTree A)
  → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) l
  → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) r
  → All (λ p → proj (snd p)  < proj x) l → All (λ p → proj x < proj (snd p)) r
  → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) (balance l x r)
balance-ordered x l r ord[l]' ord[r]' all[l]<x' all[r]>x'
  with balance-cases x l r
... | left null≡ rewrite null≡ = node (all[l]<x' , all[r]>x') ord[l]' ord[r]'
... | right (left (x₁ , refl , refl , refl)) =
  case (all[l]<x' , all[r]>x' , ord[l]' , ord[r]') of
    λ { (node x all[l]<x all[l]<x₁ , node x₁ all[r]>x all[r]>x₁ , node x₂ ord[l] ord[l]₁ , node x₃ ord[r] ord[r]₁) →
        node ((node x all[l]<x all[l]<x₁) , (node x₁ all[r]>x all[r]>x₁)) (node x₂ ord[l] ord[l]₁) (node x₃ ord[r] ord[r]₁)
      }
... | right (right (left (x₁ , left refl , snd₁))) rewrite snd₁ =
  case (ord[l]' , all[l]<x') of
    λ { (node (node x<y all[a]<y all[b]>y , all[c]>y) (node (all[a]<x , all[b]>x) ord[lll] ord[llr]) ord[lr]
         , node y<z (node x<z all[a]<z all[b]<z) all[c]<z) →
           node ((node x<y all[a]<y all[b]>y)
                , (node y<z all[c]>y (mapAll (λ z<a → less-trans y<z z<a) all[r]>x')))
                (node (all[a]<x , all[b]>x) ord[lll] ord[llr])
                (node (all[c]<z , all[r]>x') ord[lr] ord[r]')
      }
... | right (right (left (x₁ , right refl , snd₁))) rewrite snd₁ =
  case (ord[l]' , all[l]<x') of
    λ { (node (all[a]<x , node x<y all[b]>x all[c]>x) ord[a] (node (all[b]<y , all[c]>y) ord[b] ord[c])
        , node x<z all[l]<z (node y<z all[b]<z all[c]<z)) →
          node ((node x<y (mapAll (λ a<x → less-trans a<x x<y) all[a]<x) all[b]<y)
               , (node y<z all[c]>y (mapAll (λ z>a → less-trans y<z z>a) all[r]>x')))
               (node (all[a]<x , all[b]>x) ord[a] ord[b])
               (node (all[c]<z , all[r]>x') ord[c] ord[r]')
      }
... | right (right (right (x₁ , left refl , snd₁))) rewrite snd₁ =
   case (ord[r]' , all[r]>x') of
     λ { (node (all[a]<y , node y<z all[b]>y all[c]>y) ord[a] (node (all[b]<z , all[c]>z) ord[b] ord[c])
         , node x<y all[r]>x (node x<z all[b]>x all[c]>x)) →
           node ((node x<y (mapAll (λ a<x → less-trans a<x x<y) all[l]<x') all[a]<y)
                , (node y<z all[b]>y all[c]>y))
                (node (all[l]<x' , all[r]>x) ord[l]' ord[a])
                (node (all[b]<z , all[c]>z) ord[b] ord[c])
        }
... | right (right (right (x₁ , right refl , snd₁))) rewrite snd₁ =
  case (ord[r]' , all[r]>x') of
    λ { (node ((node z<y all[a]<y all[b]<y) , all[c]>y) (node (all[a]<z , all[b]>z) ord[a] ord[b]) ord[c]
        , node x<y (node x<z all[a]>x all[b]>x) all[c]>x) →
          node ((node x<z (mapAll (λ a<x → less-trans a<x x<z) all[l]<x') all[a]<z)
               , (node z<y all[b]>z (mapAll (λ a>y → less-trans z<y a>y ) all[c]>y)))
               (node (all[l]<x' , all[a]>x) ord[l]' ord[a])
               (node (all[b]<y , all[c]>y) ord[b] ord[c])
    }


balance-Any :
  ∀ {ℓ₂}
  → {P : A → Set ℓ₂}
  → (x : A) → (l : RedBlackTree A) → (r : RedBlackTree A)
  → Either (P x) (Either (Any (P ∘ snd) l) (Any (P ∘ snd) r))
  → Any (P ∘ snd) (balance l x r)
balance-Any x l r P
  with balance-cases x l r
... | left x₁ rewrite x₁ =
  case P of
    λ { (left Px) → here Px
      ; (right (left x)) → inLeft x
      ; (right (right x)) → inRight x
      }
... | right (left (_ , refl , refl , refl)) =
  case P of
    λ { (left x) → here x
      ; (right (left (here x))) → inLeft (here x)
      ; (right (left (inLeft x))) → inLeft (inLeft x)
      ; (right (left (inRight x))) → inLeft (inRight x)
      ; (right (right (here x))) → inRight (here x)
      ; (right (right (inLeft x))) → inRight (inLeft x)
      ; (right (right (inRight x))) → inRight (inRight x)
      }
... | right (right (left (x₁ , left refl , snd₁))) rewrite snd₁ =
  case P of
    λ { (left x) → inRight (here x)
      ; (right (left (here x))) → here x
      ; (right (left (inLeft (here x)))) → inLeft (here x)
      ; (right (left (inLeft (inLeft x)))) → inLeft (inLeft x)
      ; (right (left (inLeft (inRight x)))) → inLeft (inRight x)
      ; (right (left (inRight x))) → inRight (inLeft x)
      ; (right (right x)) → inRight (inRight x)
      }
... | right (right (left (x₁ , right refl , snd₁))) rewrite snd₁ =
  case P of
    λ { (left x) → inRight (here x)
      ; (right (left (here x))) → inLeft (here x)
      ; (right (left (inLeft x))) → inLeft (inLeft x)
      ; (right (left (inRight (here x)))) → here x
      ; (right (left (inRight (inLeft x)))) → inLeft (inRight x)
      ; (right (left (inRight (inRight x)))) → inRight (inLeft x)
      ; (right (right x)) → inRight (inRight x)
      }
... | right (right (right (x₁ , left refl , snd₁))) rewrite snd₁ =
  case P of
    λ { (left x) → inLeft (here x)
      ; (right (left x)) → inLeft (inLeft x)
      ; (right (right (here x))) → here x
      ; (right (right (inLeft x))) → inLeft (inRight x)
      ; (right (right (inRight (here x)))) → inRight (here x)
      ; (right (right (inRight (inLeft x)))) → inRight (inLeft x)
      ; (right (right (inRight (inRight x)))) → inRight (inRight x)
      }
... | right (right (right (x₁ , right refl , snd₁))) rewrite snd₁ =
  case P of
    λ { (left x) → inLeft (here x)
      ; (right (left x)) → inLeft (inLeft x)
      ; (right (right (here x))) → inRight (here x)
      ; (right (right (inLeft (here x)))) → here x
      ; (right (right (inLeft (inLeft x)))) → inLeft (inRight x)
      ; (right (right (inLeft (inRight x)))) → inRight (inLeft x)
      ; (right (right (inRight x))) → inRight (inRight x)
      }

balance-All :
  ∀ {ℓ₂}
  → {P : A → Set ℓ₂}
  → (x : A) → (l : RedBlackTree A) → (r : RedBlackTree A)
  → P x → All (P ∘ snd) l → All (P ∘ snd) r
  → All (P ∘ snd) (balance l x r)
balance-All x l r Px allP[l] allP[r]
  with balance-cases x l r
... | left x₁ rewrite x₁ = node Px allP[l] allP[r]
... | right (left (_ , refl , refl , refl)) =
  case (allP[l] , allP[r]) of
    λ { (node x allP[l]' allP[l]'' , node x₁ allP[r]' allP[r]'') →
        node Px (node x allP[l]' allP[l]'') (node x₁ allP[r]' allP[r]'')}
... | right (right (left (x₁ , left refl , snd₁))) rewrite snd₁ =
  case allP[l] of
    λ { (node x (node x₁ allP[l] allP[l]₂) allP[l]₁) →
        node x (node x₁ allP[l] allP[l]₂) (node Px allP[l]₁ allP[r]) }
... | right (right (left (x₁ , right refl , snd₁))) rewrite snd₁ =
  case allP[l] of
    λ { (node x allP[l] (node x₁ allP[l]₁ allP[l]₂)) →
        node x₁ (node x allP[l] allP[l]₁) (node Px allP[l]₂ allP[r])}
... | right (right (right (_ , left refl , snd₁))) rewrite snd₁ =
   case allP[r] of
     λ { (node x allP[r] (node x₁ allP[r]₁ allP[r]₂)) →
         node x (node Px allP[l] allP[r]) (node x₁ allP[r]₁ allP[r]₂)}
... | right (right (right (_ , right refl , snd₁))) rewrite snd₁ =
   case allP[r] of
     λ { (node x (node x₁ allP[r] allP[r]₂) allP[r]₁) →
         node x₁ (node Px allP[l] allP[r]) (node x allP[r]₂ allP[r]₁) }


sub1-ordered :
  {{_ : Ord/Laws B}}
  → {proj : A → B}
  → (t : RedBlackTree A)
  → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) t
  → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) (sub1 t)
sub1-ordered .leaf leaf = leaf
sub1-ordered (node (red , y) _ _) (node x₁ ord[t] ord[t]₁) =
  node x₁ ord[t] ord[t]₁
sub1-ordered (node (black , y) _ _) (node x₁ ord[t] ord[t]₁) =
  node x₁ ord[t] ord[t]₁

sub1-All :
     {P : A → Set ℓ₂}
   → (t : RedBlackTree A)
   → All (P ∘ snd) t
   → All (P ∘ snd) (sub1 t)
sub1-All .leaf leaf = leaf
sub1-All (node (red , x) _ _) (node Px all[t] all[t]₁) = node Px all[t] all[t]₁
sub1-All (node (black , x) _ _) (node Px all[t] all[t]₁) = node Px all[t] all[t]₁


sub1-Any :
     {P : A → Set ℓ₂}
   → (t : RedBlackTree A)
   → Any (P ∘ snd) t
   → Any (P ∘ snd) (sub1 t)
sub1-Any leaf ()
sub1-Any (node (red , x) l r) (here Px) = here Px
sub1-Any (node (black , x) l r) (here Px) = here Px
sub1-Any (node (red , x) l r) (inLeft any[l]) = inLeft any[l]
sub1-Any (node (black , x) l r) (inLeft any[l]) = inLeft any[l]
sub1-Any (node (red , x) l r) (inRight any[r]) = inRight any[r]
sub1-Any (node (black , x) l r) (inRight any[r]) = inRight any[r]

balleft-cases :
  (v : A) → (l : RedBlackTree A) → (r : RedBlackTree A)
  → (Either (Σ (A × RB A × RB A) (λ { (x , a , b) →
                     l ≡ (node (red , x) a b)
                     × balleft l v r ≡ node (red , v) (node (black , x) a b) r
                    }))
    (Either (Σ (A × RB A × RB A) (λ { (y , a , b) →
                    r ≡ (node (black , y) a b)
                    × balleft l v r ≡ balance l v (node (red , y) a b)
                   }))
    (Either (Σ (A × A × RB A × RB A × RB A)  (λ { (z , y , a , b , c) →
                    r ≡ (node (red , z) (node (black , y) a b) c)
                    × balleft l v r ≡ node (red , y) (node (black , v) l a) (balance b z (sub1 c))
                   }))
             (balleft l v r ≡ node (red , v) l r)
             )))
balleft-cases v leaf leaf = right (right (right refl))
balleft-cases v leaf (node (red , snd₁) leaf r₁) =
  right (right (right refl))
balleft-cases v leaf (node (red , snd₁) (node (red , snd₂) r r₂) r₁) =
  right (right (right refl))
balleft-cases v leaf (node (red , snd₁) (node (black , snd₂) r r₂) r₁) =
  right (right (left (_ , (refl  , refl))))
balleft-cases v leaf (node (black , snd₁) r r₁) =
  right (left (_ , refl , refl))
balleft-cases v (node (red , snd₁) l l₁) leaf = left (_ , refl , refl)
balleft-cases v (node (black , snd₁) l l₁) leaf = right (right (right refl))
balleft-cases v (node (red , snd₁) l l₁) (node (red , snd₂) r r₁) = left (_ , refl , refl)
balleft-cases v (node (red , snd₁) l l₁) (node (black , snd₂) r r₁) = left (_ , refl , refl)
balleft-cases v (node (black , snd₁) l l₁) (node (red , snd₂) leaf leaf) =
  right (right (right refl))
balleft-cases v (node (black , snd₁) l l₁) (node (red , snd₂) leaf (node _ r₁ r₂)) =
  right (right (right refl))
balleft-cases v (node (black , snd₁) l l₁) (node (red , snd₂) (node (red , snd₃) r r₂) _) =
 right (right (right refl))
balleft-cases v (node (black , snd₁) l l₁) (node (red , snd₂) (node (black , snd₃) r r₂) _) =
  right (right (left (_ , refl , refl)))
balleft-cases v (node (black , snd₁) l l₁) (node (black , snd₂) _ _) =
  right (left (_ , refl , refl))

balleft-ordered :
  {{_ : Ord/Laws B}}
  → {proj : A → B}
  → (x : A) → (l : RedBlackTree A) → (r : RedBlackTree A)
  → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) l
  → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) r
  → All (λ p → proj (snd p)  < proj x) l → All (λ p → proj x < proj (snd p)) r
  → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) (balleft l x r)
balleft-ordered x l r ord[l] ord[r] all[l]<x all[r]>x
  with balleft-cases x l r
... | left (_ , refl , refl) =
  case (all[l]<x , ord[l]) of
    λ { (node x all[l]<x' all[l]<x'' , node x₁ ord[l]' ord[l]'') →
        node ((node x all[l]<x' all[l]<x'') , all[r]>x) (node x₁ ord[l]' ord[l]'') ord[r]
      }
... | right (left (_ , refl , snd₁)) rewrite snd₁ =
  case (all[r]>x , ord[r]) of
    λ { (node x all[r]>x' all[r]>x'' , node x₁ ord[r]' ord[r]'') →
      balance-ordered
        _ _ _ ord[l]
        (node x₁ ord[r]' ord[r]'') all[l]<x
        (node x all[r]>x' all[r]>x'')
      }
... | right (right (left ((z , y , a , b , c) , refl , snd₁))) rewrite snd₁ =
  case (all[r]>x , ord[r]) of
    λ { (node x<z (node x<y all[a]>x all[b]>x) all[c]>x , node (node y<z all[a]<z all[b]<z , all[c]>z) (node (all[a]<y , all[b]>y) ord[a] ord[b]) ord[c]) →
      node ((node x<y (mapAll (λ a<x → less-trans a<x x<y) all[l]<x ) all[a]<y)
           , balance-All _ _ _ y<z all[b]>y (sub1-All _ (mapAll (λ z<a → less-trans y<z z<a) all[c]>z))
           )
           (node (all[l]<x , all[a]>x) ord[l] ord[a])
           (balance-ordered z b (sub1 c) ord[b] (sub1-ordered c ord[c]) all[b]<z (sub1-All c all[c]>z))
      }
... | right (right (right x₁)) rewrite x₁ =
   node (all[l]<x , all[r]>x) ord[l] ord[r]

balleft-Any :
  {P : A → Set ℓ₂}
  → (v : A) → (l : RedBlackTree A) → (r : RedBlackTree A)
  → Either (P v) (Either (Any (P ∘ snd) l) (Any (P ∘ snd) r))
  → Any (P ∘ snd) (balleft l v r)
balleft-Any v l r inArgs
  with balleft-cases v l r
... | left ((x , a , b) , refl , refl) =
  case inArgs of
    λ { (left Pv) → here Pv ; (right (left (here Px))) → inLeft (here Px)
      ; (right (left (inLeft any[a]))) → inLeft (inLeft any[a])
      ; (right (left (inRight any[b]))) → inLeft (inRight any[b])
      ; (right (right any[r])) → inRight any[r]
      }
... | right (left ((x , a , b) , refl , balleft≡)) rewrite balleft≡ =
  case inArgs of
    λ { (left Pv) → balance-Any v l _ (left Pv)
      ; (right (left (here Px))) → balance-Any v l _ (right (left (here Px)))
      ; (right (left (inLeft any[l₁]))) → balance-Any v _ _ (right (left (inLeft any[l₁])))
      ; (right (left (inRight any[r₁]))) → balance-Any v _ _ (right (left (inRight any[r₁])))
      ; (right (right (here Px))) → balance-Any v _ _ (right (right (here Px)))
      ; (right (right (inLeft any[a]))) → balance-Any v _ _ (right (right (inLeft any[a])))
      ; (right (right (inRight any[b]))) → balance-Any v _ _ (right (right (inRight any[b])))
      }
... | right (right (left ((z , y , a , b , c) , refl , balleft≡))) rewrite balleft≡ =
  case inArgs of
    λ { (left Pv) → inLeft (here Pv)
      ; (right (left any[l])) → inLeft (inLeft any[l])
      ; (right (right (here Pz))) → inRight (balance-Any z _ _ (left Pz))
      ; (right (right (inLeft (here Py)))) → here Py
      ; (right (right (inLeft (inLeft any[a])))) → inLeft (inRight any[a])
      ; (right (right (inLeft (inRight any[b])))) → inRight (balance-Any z _ _ (right (left any[b])))
      ; (right (right (inRight any[c]))) → inRight (balance-Any z _ (sub1 c) (right (right (sub1-Any c any[c]))))
      }
... | right (right (right balleft≡)) rewrite balleft≡ =
  case inArgs of
    λ { (left Pv) → here Pv ; (right (left any[l])) → inLeft any[l] ; (right (right any[r])) → inRight any[r] }

balleft-All :
  {P : A → Set ℓ₂}
  → (x : A) → (l : RedBlackTree A) → (r : RedBlackTree A)
  → P x
  → All (P ∘ snd) l → All (P ∘ snd) r
  → All (P ∘ snd) (balleft l x r)
balleft-All x l r Px all[l] all[r]
  with balleft-cases x l r
... | left (_ , refl , refl) =
  case all[l] of
    λ { (node x all[l] all[l]₁) → node Px (node x all[l] all[l]₁) all[r] }
... | right (left ((y , a , b) , refl , balleft≡)) rewrite balleft≡  =
  case all[r] of
    λ { (node Py all[a] all[b]) → balance-All x l (node (red , y) a b) Px all[l] (node Py all[a] all[b]) }
... | right (right (left ((z , y , a , b , c) , refl , balleft≡))) rewrite balleft≡ =
  case all[r] of
    λ { (node Pz (node Py all[a] all[b]) all[c]) →
      node Py (node Px all[l] all[a]) (balance-All z b (sub1 c) Pz all[b] (sub1-All c all[c])) }
... | right (right (right balleft≡)) rewrite balleft≡ = node Px all[l] all[r]


balright-cases :
  (v : A) → (l : RedBlackTree A) → (r : RedBlackTree A)
  → (Either (Σ (A × RB A × RB A) (λ { (y , a , b) →
                     r ≡ node (red , y) a b
                     × balright l v r ≡ node (red , v) l (node (black , y) a b)
                    }))
    (Either (Σ (A × RB A × RB A) (λ { (x , a , b) →
                    l ≡ node (black , x) a b
                    × balright l v r ≡ balance (node (red , x) a b) v r
                   }))
    (Either (Σ (A × A × RB A × RB A × RB A)  (λ { (x , y , a , b , c) →
                    l ≡ (node (red , x) a (node (black , y) b c))
                    × balright l v r ≡ node (red , y) (balance (sub1 a) x b) (node (black , v) c r)
                   }))
             (balright l v r ≡ node (red ,  v) l r)
             )))
balright-cases v leaf leaf = right (right (right refl))
balright-cases v leaf (node (red , snd₁) r r₁) = left (_ , refl , refl)
balright-cases v leaf (node (black , snd₁) r r₁) = right (right (right refl))
balright-cases v (node (red , snd₁) l leaf) leaf = right (right (right refl))
balright-cases v (node (red , snd₁) l (node (red , snd₂) l₁ l₂)) leaf = right (right (right refl))
balright-cases v (node (red , snd₁) l (node (black , snd₂) l₁ l₂)) leaf = right (right (left (_ , refl , refl)))
balright-cases v (node (black , snd₁) l l₁) leaf = right (left (_ , refl , refl))
balright-cases v (node (red , snd₁) l l₁) (node (red , snd₂) r r₁) = left (_ , refl , refl)
balright-cases v (node (red , snd₁) l leaf) (node (black , snd₂) r r₁) = right (right (right refl))
balright-cases v (node (red , snd₁) l (node (red , snd₃) l₁ l₂)) (node (black , snd₂) r r₁) =
  right (right (right refl))
balright-cases v (node (red , snd₁) l (node (black , snd₃) l₁ l₂)) (node (black , snd₂) r r₁) =
  right (right (left (_ , refl , refl)))
balright-cases v (node (black , snd₁) l l₁) (node (red , snd₂) r r₁) = right (left (_ , refl , refl))
balright-cases v (node (black , snd₁) l l₁) (node (black , snd₂) r r₁) = right (left (_ , refl , refl))

balright-ordered :
  {{_ : Ord/Laws B}}
  → {proj : A → B}
  → (x : A) → (l : RedBlackTree A) → (r : RedBlackTree A)
  → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) l
  → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) r
  → All (λ p → proj (snd p) < proj x) l → All (λ p → proj x < proj (snd p)) r
  → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) (balright l x r)
balright-ordered v l r ord[l] ord[r] all[l]<v all[r]>v
  with balright-cases v l r
... | left (_ , refl , refl) =
  case (ord[r] , all[r]>v) of
    λ { (node x ord[r] ord[r]₁ , node x₁ all[r]>v all[r]>v₁) →
     node (all[l]<v , (node x₁ all[r]>v all[r]>v₁)) ord[l] (node x ord[r] ord[r]₁) }
... | right (left ((x , a , b) , refl , snd₁)) rewrite snd₁ =
  case ( ord[l] , all[l]<v ) of
    λ { (node x ord[l] ord[l]₁ , node x₁ all[l]<x all[l]<x₁) →
      balance-ordered
        _ _ _
        (node x ord[l] ord[l]₁) ord[r]
        (node x₁ all[l]<x all[l]<x₁) all[r]>v
      }
... | right (right (left ((x , y , a , b , c) , refl , snd₁))) rewrite snd₁ =
  case (ord[l] , all[l]<v) of
    λ { (node (all[a]<x , node x<y all[b]>x all[c]>x) ord[a] (node (all[b]<y , all[c]>y) ord[b] ord[c])
        , node x<v all[a]<v (node y<v all[b]<v all[c]<v)) →
        node ( balance-All x (sub1 a) b x<y ((sub1-All a (mapAll (λ a<x → less-trans a<x x<y ) all[a]<x))) all[b]<y
             , (node y<v all[c]>y (mapAll (λ v<a → less-trans y<v v<a) all[r]>v)))
             (balance-ordered x (sub1 a) b (sub1-ordered a ord[a]) ord[b] (sub1-All a all[a]<x) all[b]>x)
             (node (all[c]<v , all[r]>v) ord[c] ord[r])  }
... | right (right (right x)) rewrite x = node (all[l]<v , all[r]>v) ord[l] ord[r]


balright-All :
  {P : A → Set ℓ₂}
  → (x : A) → (l : RedBlackTree A) → (r : RedBlackTree A)
  → P x
  → All (P ∘ snd) l → All (P ∘ snd) r
  → All (P ∘ snd) (balright l x r)
balright-All x l r Px all[l] all[r]
  with balright-cases x l r
... | left (_ , refl , refl) =
  case all[r] of
    λ { (node Py all[a] all[b]) → node Px all[l] (node Py all[a] all[b]) }
... | right (left ((y , a , b) , refl , balright≡)) rewrite balright≡  =
  case all[l] of
    λ { (node Py all[a] all[b]) → balance-All x (node (red , y) a b) r Px (node Py all[a] all[b]) all[r]
      }
... | right (right (left ((z , y , a , b , c) , refl , balright≡))) rewrite balright≡ =
  case all[l] of
    λ { (node Pz all[a] (node Py all[b] all[c])) →
        node Py (balance-All z (sub1 a) b Pz (sub1-All a all[a]) all[b]) (node Px all[c] all[r])
      }
... | right (right (right balright≡)) rewrite balright≡ = node Px all[l] all[r]


balright-Any :
  {P : A → Set ℓ₂}
  → (v : A) → (l : RedBlackTree A) → (r : RedBlackTree A)
  → Either (P v) (Either (Any (P ∘ snd) l) (Any (P ∘ snd) r))
  → Any (P ∘ snd) (balright l v r)
balright-Any v l r inArgs
  with balright-cases v l r
... | left ((x , a , b) , refl , refl) =
  case inArgs of
    λ { (left x) → here x
      ; (right (left inl)) → inLeft inl
      ; (right (right (here x))) → inRight (here x)
      ; (right (right (inLeft inl))) → inRight (inLeft inl)
      ; (right (right (inRight inr))) → inRight (inRight inr)
      }
... | right (left ((x , a , b) , refl , balright≡)) rewrite balright≡ =
  case inArgs of
    λ { (left Pv) → balance-Any v _ _ (left Pv)
      ; (right (left (here Px))) → balance-Any v _ _ (right (left (here Px)))
      ; (right (left (inLeft ina))) → balance-Any v _ _ (right (left (inLeft ina)))
      ; (right (left (inRight inb))) → balance-Any v _ _ (right (left (inRight inb)))
      ; (right (right inr)) → balance-Any v _ _ (right (right inr))
      }
... | right (right (left ((z , y , a , b , c) , refl , balright≡))) rewrite balright≡ =
  case inArgs of
    λ { (left Pv) → inRight (here Pv)
      ; (right (left (here Pz))) → inLeft (balance-Any z _ _ (left Pz))
      ; (right (left (inLeft ina))) → inLeft (balance-Any z (sub1 a) _ (right (left (sub1-Any a ina))))
      ; (right (left (inRight (here Py)))) → here Py
      ; (right (left (inRight (inLeft inb)))) → inLeft (balance-Any z _ _ (right (right inb)))
      ; (right (left (inRight (inRight inc)))) → inRight (inLeft inc)
      ; (right (right inr)) → inRight (inRight inr)
      }
... | right (right (right balright≡)) rewrite balright≡ =
  case inArgs of
    λ { (left Pv) → here Pv
      ; (right (left any[l])) → inLeft any[l]
      ; (right (right any[r])) → inRight any[r]
      }


app-All :
  ∀ {ℓ₂}
  {P : A → Set ℓ₂}
  → (l : RedBlackTree A) → (r : RedBlackTree A)
  → All (P ∘ snd) l → All (P ∘ snd) r
  → All (P ∘ snd) (app l r)
app-All leaf leaf leaf leaf = leaf
app-All leaf (node x r r₁) leaf (node x₁ all[r] all[r]₁) = node x₁ all[r] all[r]₁
app-All (node x l l₁) leaf (node x₁ all[l] all[l]₁) leaf = node x₁ all[l] all[l]₁
app-All (node (red , x) a b) (node (red , y) c d) (node Px all[a] all[b]) (node Py all[c] all[d])
  with app b c | app-All b c all[b] all[c]
... | leaf | leaf =
  node Px all[a] (node Py leaf all[d])
... | node (red , z) b' c' | node Pz all[b'] all[c'] =
  node Pz (node Px all[a] all[b']) (node Py all[c'] all[d])
... | node (black , z) b' c' | node Pz all[b'] all[c'] =
  node Px all[a] (node Py (node Pz all[b'] all[c']) all[d])
app-All (node (red , x) a b) (node (black , y) c d) (node Px all[a] all[b]) (node Py all[c] all[d]) =
  node Px all[a] (app-All b _ all[b] (node Py all[c] all[d]))
app-All (node (black , x) a b) (node (red , y) c d) (node Px all[a] all[b]) (node Py all[c] all[d]) =
  node Py (app-All (node (black , x) a b) c (node Px all[a] all[b]) all[c]) all[d]
app-All (node (black , x) a b) (node (black , y) c d) (node Px all[a] all[b]) (node Py all[c] all[d])
  with app b c | app-All b c all[b] all[c]
... | leaf | leaf =
  balleft-All x a (node (black , y) leaf d) Px all[a] (node Py leaf all[d])
... | node (red , snd₁) rec rec₁ | node x₂ all[rec] all[rec]₁ =
  node x₂ (node Px all[a] all[rec]) (node Py all[rec]₁ all[d])
... | node (black , snd₁) rec rec₁ | node x₂ all[rec] all[rec]₁ =
  balleft-All x a _ Px all[a] (node Py (node x₂ all[rec] all[rec]₁) all[d])

app-Any :
    {P : A → Set ℓ₂}
  → (l : RedBlackTree A) → (r : RedBlackTree A)
  → Either (Any (P ∘ snd) l) (Any (P ∘ snd) r)
  → Any (P ∘ snd) (app l r)
app-Any leaf leaf (left ())
app-Any leaf leaf (right ())
app-Any leaf (node x a b) (right anyP) = anyP
app-Any (node x a b) leaf (left anyP) = anyP
app-Any (node (red , x) a b) (node (red , y) c d) (left (here Px))
  with app b c
...| leaf = here Px
...| (node (red , z) b' c') = inLeft (here Px)
...| (node (black , z) b' c') = here Px
app-Any (node (red , x) a b) (node (red , y) c d) (left (inLeft any[a]))
  with app b c
...| leaf = inLeft any[a]
...| (node (red , z) b' c') = inLeft (inLeft any[a])
...| (node (black , z) b' c') = inLeft any[a]
app-Any (node (red , x) a b) (node (red , y) c d) (left (inRight any[b]))
  with app b c | app-Any b c (left any[b])
...| (node (red , z) b' c') | any[app] =
  case any[app] of
    λ { (here Pz) → here Pz ; (inLeft any[b']) → inLeft (inRight any[b'])
      ; (inRight any[app]) → inRight (inLeft any[app]) }
...| (node (black , z) b' c') | any[app] = inRight (inLeft any[app])
app-Any (node (red , x) a b) (node (red , y) c d) (right (here Py))
  with app b c
...| leaf = inRight (here Py)
...| (node (red , z) b' c') = inRight (here Py)
...| (node (black , z) b' c') = inRight (here Py)
app-Any (node (red , x) a b) (node (red , y) c d) (right (inLeft any[c]))
  with app b c | app-Any b c (right any[c])
...| (node (red , z) b' c') | any[app] =
  case any[app] of
    λ { (here Pz) → here Pz ; (inLeft any[b']) → inLeft (inRight any[b'])
      ; (inRight any[app]) → inRight (inLeft any[app]) }
...| (node (black , z) b' c') | any[app] = inRight (inLeft any[app])
app-Any (node (red , x) a b) (node (red , y) c d) (right (inRight any[d]))
  with app b c
...| leaf = inRight (inRight any[d])
...| (node (red , z) b' c') = inRight (inRight any[d])
...| (node (black , z) b' c') = inRight (inRight any[d])
app-Any (node (red , x) a b) (node (black , y) c d) (left (here Px)) = here Px
app-Any (node (red , x) a b) (node (black , y) c d) (left (inLeft any[a])) = inLeft any[a]
app-Any (node (red , x) a b) (node (black , y) c d) (left (inRight any[b])) =
  inRight (app-Any b _ (left any[b]))
app-Any (node (red , x) a b) (node (black , y) c d) (right (here Py)) =
  inRight (app-Any b _ (right (here Py)))
app-Any (node (red , x) a b) (node (black , y) c d) (right (inLeft any[c])) =
  inRight (app-Any b _ (right (inLeft any[c])))
app-Any (node (red , x) a b) (node (black , y) c d) (right (inRight any[d])) =
  inRight (app-Any b _ (right (inRight any[d])))
app-Any l@(node (black , x) a b) (node (red , y) c d) (left any[l]) =
  inLeft (app-Any l c (left any[l]))
app-Any (node (black , x) a b) (node (red , y) c d) (right (here Py)) = here Py
app-Any (node (black , x) a b) (node (red , y) c d) (right (inLeft any[c])) =
  inLeft (app-Any (node (black , x) a b) c (right any[c]))
app-Any (node (black , x) a b) (node (red , y) c d) (right (inRight any[d])) = inRight any[d]
app-Any (node (black , x) a b) (node (black , y) c d) (left (here Px))
  with app b c
...| leaf = balleft-Any x a _ (left Px)
...| (node (red , z) b' c') = inLeft (here Px)
...| (node (black , z) b' c') = balleft-Any x a (node (black , y) (node (black , z) b' c') d) (left Px)
app-Any (node (black , x) a b) (node (black , y) c d) (left (inLeft any[a]))
  with app b c
...| leaf = balleft-Any x a _ (right (left any[a]))
...| (node (red , z) b' c') = inLeft (inLeft any[a])
...| (node (black , z) b' c') = balleft-Any x a _ (right (left any[a]))
app-Any (node (black , x) a b) (node (black , y) c d) (left (inRight any[b]))
  with app b c | app-Any b c (left any[b])
... | node (red , z) b' c' | here Pz = here Pz
... | node (red , z) b' c' | inLeft any[b'] = inLeft (inRight any[b'])
... | node (red , z) b' c' | inRight any[c'] = inRight (inLeft any[c'])
... | node (black , z) b' c' | here Pz = balleft-Any x a (node _ (node (black , z) b' c') d) (right (right (inLeft (here Pz))))
... | node (black , z) b' c' | inLeft any[b'] = balleft-Any x a (node _ (node (black , z) b' c') d) (right (right (inLeft (inLeft any[b']))))
... | node (black , z) b' c' | inRight any[c'] = balleft-Any x a (node _ (node (black , z) b' c') d) (right (right (inLeft (inRight any[c']))))
app-Any (node (black , x) a b) (node (black , y) c d) (right (here Py))
  with app b c
...| leaf = balleft-Any x a _ (right (right (here Py)))
...| (node (red , z) b' c') = inRight (here Py)
...| (node (black , z) b' c') = balleft-Any x a (node (black , y) (node (black , z) b' c') d) (right (right (here Py)))
app-Any (node (black , x) a b) (node (black , y) c d) (right (inLeft any[c]))
  with app b c | app-Any b c (right any[c])
... | node (red , z) b' c' | here Pz = (here Pz)
... | node (red , z) b' c' | inLeft any[b'] = inLeft (inRight any[b'])
... | node (red , z) b' c' | inRight any[c'] = inRight (inLeft any[c'])
... | node (black , z) b' c' | here Pz = balleft-Any x a _ (right (right (inLeft (here Pz))))
... | node (black , z) b' c' | inLeft any[b'] = balleft-Any x a _ (right (right (inLeft (inLeft any[b']))))
... | node (black , z) b' c' | inRight any[c'] = balleft-Any x a _ (right (right (inLeft (inRight any[c']))))
app-Any (node (black , x) a b) (node (black , y) c d) (right (inRight any[d]))
  with app b c
...| leaf = balleft-Any x a _ (right (right (inRight any[d])))
...| node (red , z) b' c' = inRight (inRight any[d])
...| node (black , z) b' c' = balleft-Any x a _ (right (right (inRight any[d])))

app-ordered :
    {{_ : Ord/Laws B}}
  → {proj : A → B}
  → (v : A) → (l : RedBlackTree A) → (r : RedBlackTree A)
  → All (λ p → proj (snd p) < proj v) l
  → All (λ p → proj (snd p) > proj v) r
  → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) l
  → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) r
  → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) (app l r)
app-ordered _ leaf leaf _ _ leaf leaf = leaf
app-ordered v leaf (node x r r₁) _ _ leaf (node x₁ ord[r] ord[r]₁) = node x₁ ord[r] ord[r]₁
app-ordered _ (node x l l₁) leaf _ _ (node x₁ ord[l] ord[l]₁) leaf = node x₁ ord[l] ord[l]₁
app-ordered v (node (red , x) a b) (node (red , y) c d)
            (node x<v _ all[b]<v) (node y>v all[c]>z _)
            (node (all[a]<x , all[b]>x) ord[a] ord[b]) (node (all[c]<y , all[d]>y) ord[c] ord[d])
  with app b c | app-ordered v b c all[b]<v all[c]>z ord[b] ord[c]
     | app-All b c all[b]>x (mapAll (λ a>v → less-trans x<v a>v) all[c]>z)
     | app-All b c (mapAll (λ a<v → (less-trans a<v y>v)) all[b]<v) all[c]<y
... | leaf | leaf | _ | _ =
  node (all[a]<x , node (less-trans x<v y>v) leaf (mapAll (λ y<a → less-trans (less-trans x<v y>v) y<a) all[d]>y))
       ord[a]
       (node (leaf , all[d]>y) leaf ord[d])
... | node (red , z) b' c' | node (all[b']<z , all[c']>z) ord[b'] ord[c'] | (node x<z all[b']<x all[c']<x) | (node z<y all[b']<y all[c']<y) =
  node ((node x<z (mapAll (λ a<x → less-trans a<x x<z) all[a]<x) all[b']<z)
        , (node z<y all[c']>z (mapAll (λ a>y → less-trans z<y a>y) all[d]>y)))
       (node (all[a]<x , all[b']<x) ord[a] ord[b'])
       (node (all[c']<y , all[d]>y) ord[c'] ord[d])
... | node (black , z) b' c' | node x₂ ord[rec] ord[rec]₁ | (node x<z all[b']<x all[c']<x) | (node z<y all[b']<y all[c']<y) =
  node (all[a]<x ,
       (node (less-trans x<v y>v)
             (node x<z all[b']<x all[c']<x)
             (mapAll (λ y<a → less-trans x<z (less-trans z<y y<a)) all[d]>y)))
       ord[a]
       (node ((node z<y all[b']<y all[c']<y) , all[d]>y) (node x₂ ord[rec] ord[rec]₁) ord[d])
app-ordered v (node (red , x) a b) (node (black , y) c d)
            (node x<v all[a]<v all[b]<v) (node y>v all[c]>v all[d]>v)
            (node (all[a]<x , all[b]>x) ord[a] ord[b]) (node Py ord[c] ord[d]) =
  node (all[a]<x
       , app-All b (node (black , y) c d) all[b]>x
                   (node (less-trans x<v y>v)
                         (mapAll (λ a>v → less-trans x<v a>v) all[c]>v)
                         (mapAll (λ a>v → less-trans x<v a>v) all[d]>v)))
       ord[a]
       (app-ordered v b (node (black , y) c d) all[b]<v (node y>v all[c]>v all[d]>v) ord[b] (node Py ord[c] ord[d]))
app-ordered v (node (black , x) a b) (node (red , y) c d)
            (node x<v all[a]<v all[b]<v) (node y>v all[c]>v all[d]>v)
            (node Px ord[a] ord[b]) (node (all[c]<y , all[d]>y) ord[c] ord[d]) =
  node (app-All (node (black , x) a b) c
                (node (less-trans x<v y>v)
                (mapAll (λ a<v → less-trans a<v y>v) all[a]<v)
                (mapAll (λ a<v → less-trans a<v y>v) all[b]<v))
                all[c]<y
       , all[d]>y)
       (app-ordered v (node (black , x) a b) c (node x<v all[a]<v all[b]<v) all[c]>v (node Px ord[a] ord[b]) ord[c])
       ord[d]
app-ordered v (node (black , x) a b) (node (black , y) c d)
            (node x<v _ all[b]<v) (node y>v all[c]>z _)
            (node (all[a]<x , all[b]>x) ord[a] ord[b]) (node (all[c]<y , all[d]>y) ord[c] ord[d])
  with app b c | app-ordered v b c all[b]<v all[c]>z ord[b] ord[c]
     | app-All b c all[b]>x (mapAll (λ a>v → less-trans x<v a>v) all[c]>z)
     | app-All b c (mapAll (λ a<v → (less-trans a<v y>v)) all[b]<v) all[c]<y
... | leaf | leaf | _ | _ =
  balleft-ordered x a (node (black , y) leaf d) ord[a]
                  (node (leaf , all[d]>y) leaf ord[d]) all[a]<x
                  (node (less-trans x<v y>v) leaf (mapAll (λ y>a → less-trans (less-trans x<v y>v) y>a) all[d]>y))
... | node (red , z) b' c' | node (all[b']<z , all[c']>z) ord[b'] ord[c'] | (node x<z all[b']<x all[c']<x) | (node z<y all[b']<y all[c']<y) =
  node ((node x<z (mapAll (λ a<x → less-trans a<x x<z) all[a]<x) all[b']<z)
       , node z<y all[c']>z (mapAll (λ y<a → less-trans z<y y<a) all[d]>y))
       (node (all[a]<x , all[b']<x) ord[a] ord[b'])
       (node (all[c']<y , all[d]>y) ord[c'] ord[d])
... | node (black , z) b' c' | node (all[b']<z , all[c']>z) ord[rec] ord[rec]₁ | (node x<z all[b']<x all[c']<x) | (node z<y all[b']<y all[c']<y) =
  balleft-ordered
    x a (node (black , y) (node (black , z) b' c') d)
    ord[a]
    (node (node z<y all[b']<y all[c']<y , all[d]>y)
          (node (all[b']<z , all[c']>z) ord[rec] ord[rec]₁) ord[d])
    all[a]<x
    (node (less-trans x<z z<y)
          (node x<z all[b']<x all[c']<x)
          (mapAll (λ y<a → less-trans (less-trans x<z z<y) y<a) all[d]>y))



mutual
  delformLeft-All :
      {P : A → Set ℓ₂}
      → {{OrdB : Ord/Laws B}}
      → (proj : A → B)
      → (k : B)
      → (l : RedBlackTree A) → (y : A) → (r : RedBlackTree A)
      → (P y)
      → All (P ∘ snd) l → All (P ∘ snd) r
      → All (P ∘ snd) (delformLeft proj k l y r)
  delformLeft-All proj k leaf y r Py leaf all[r] =
    node Py leaf all[r]
  delformLeft-All proj k a@(node (red , x) b c) y r Py all[a]@(node Px all[b] all[c]) all[r] =
    node Py (del-All proj k a all[a]) all[r]
  delformLeft-All proj k a@(node (black , _) _ _) y r Py all[a]@(node _ _ _) all[r] =
    balleft-All y (del proj k a) r Py (del-All proj k a all[a]) all[r]

  delformRight-All :
      {P : A → Set ℓ₂}
      → {{_ : Ord/Laws B}}
      → (proj : A → B)
      → (k : B)
      → (l : RedBlackTree A) → (y : A) → (r : RedBlackTree A)
      → (P y)
      → All (P ∘ snd) l → All (P ∘ snd) r
      → All (P ∘ snd) (delformRight proj k l y r)
  delformRight-All proj k l y leaf Py all[l] all[r] =
    node Py all[l] all[r]
  delformRight-All proj k l y r@(node (red , _) _ _) Py all[l] all[r] =
    node Py all[l] (del-All proj k r all[r])
  delformRight-All proj k l y r@(node (black , _) _ _) Py all[l] all[r] =
    balright-All y l (del proj k r) Py all[l] (del-All proj k r all[r])


  del-All :
      {P : A → Set ℓ₂}
      → {{_ : Ord/Laws B}}
      → (proj : A → B)
      → (k : B)
      → (t : RedBlackTree A)
      → All (P ∘ snd) t
      → All (P ∘ snd) (del proj k t)
  del-All proj k leaf all[t] = leaf
  del-All proj k (node (_ , y) a b) (node Py all[a] all[b])
    with compare k (proj y)
  ... | less lt = delformLeft-All proj k a y b Py all[a] all[b]
  ... | equal eq = app-All a b all[a] all[b]
  ... | greater gt = delformRight-All proj k a y b Py all[a] all[b]



mutual
  delformLeft-ordered :
      {{_ : Ord/Laws B}}
      → (proj : A → B)
      → (k : B)
      → (l : RedBlackTree A) → (y : A) → (r : RedBlackTree A)
      → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) l
      → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) r
      → All (λ p → proj (snd p)  < proj y) l → All (λ p → proj y < proj (snd p)) r
      → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) (delformLeft proj k l y r)
  delformLeft-ordered proj k leaf y r ord[l] ord[r] all[l]<y all[r]>y =
    node (all[l]<y , all[r]>y) ord[l] ord[r]
  delformLeft-ordered proj k l@(node (red , _) _ _) y r ord[l] ord[r] all[l]<y all[r]>y =
    node (del-All proj k l all[l]<y , all[r]>y)
         (del-ordered proj k l ord[l]) ord[r]
  delformLeft-ordered proj k l@(node (black , _) _ _) y r ord[l] ord[r] all[l]<y all[r]>y =
    balleft-ordered
      y (del proj k l) r
      (del-ordered proj k l ord[l]) ord[r]
      (del-All proj k l all[l]<y) all[r]>y

  delformRight-ordered :
      {{_ : Ord/Laws B}}
      → (proj : A → B)
      → (k : B)
      → (l : RedBlackTree A) → (y : A) → (r : RedBlackTree A)
      → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) l
      → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) r
      → All (λ p → proj (snd p)  < proj y) l → All (λ p → proj y < proj (snd p)) r
      → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) (delformRight proj k l y r)
  delformRight-ordered proj k l y leaf ord[l] ord[r] all[l]<y all[r]>y =
    node (all[l]<y , all[r]>y) ord[l] ord[r]
  delformRight-ordered proj k l y r@(node (red , _) _ _) ord[l] ord[r] all[l]<y all[r]>y =
    node (all[l]<y , (del-All proj k r all[r]>y))
         ord[l] (del-ordered proj k r ord[r])
  delformRight-ordered proj k l y r@(node (black , _) _ _) ord[l] ord[r] all[l]<y all[r]>y =
    balright-ordered y l (del proj k r)
      ord[l] (del-ordered proj k r ord[r])
      all[l]<y (del-All proj k r all[r]>y)


  del-ordered :
      {{_ : Ord/Laws B}}
      → (proj : A → B)
      → (k : B)
      → (t : RedBlackTree A)
      → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) t
      → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) (del proj k t)
  del-ordered proj k leaf ord[t] = leaf
  del-ordered proj k (node (_ , y) l r) (node (all[l]<y , all[r]>y) ord[l] ord[r])
    with compare k (proj y)
  ... | less lt = delformLeft-ordered proj k l y r ord[l] ord[r] all[l]<y all[r]>y
  ... | equal eq = app-ordered y l r all[l]<y all[r]>y ord[l] ord[r]
  ... | greater gt = delformRight-ordered proj k l y r ord[l] ord[r] all[l]<y all[r]>y

deleteProj-ordered :
   {{_ : Ord/Laws B}}
   → (proj : A → B)
   → (b : B)
   → (t : RedBlackTree A)
   → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) t
   → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) (deleteProj proj b t)
deleteProj-ordered proj b t ord[t]
  with del proj b t | del-ordered proj b t ord[t]
... | leaf | leaf = leaf
... | node (_ , y) l r | node (all[l]<y , all[r]>y) ord[l] ord[r] =
  node (all[l]<y , all[r]>y) ord[l] ord[r]



mutual

  delformLeft-RBMember :
    {{_ : Ord/Laws B}}
    → (proj : A → B)
    → (b : B)
    → (l : RedBlackTree A) → (y : A) → (r : RedBlackTree A)
    → (b < proj y)
    → All (λ p → proj (snd p)  < proj y) l → All (λ p → proj y < proj (snd p)) r
    → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) l
    → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) r
    → All (λ p → (proj (snd p) ≢ b)
               × Either ((snd p) ≡ y)
                (Either (RBMember (snd p) l)
                        (RBMember (snd p) r)))
          (delformLeft proj b l y r)
  delformLeft-RBMember proj b leaf y r b<y all[l]<y all[r]>y ord[l] ord[r] =
    node ((λ y≡b → less-antirefl (transport (b <_) y≡b b<y)) , left refl)
         leaf (mapAll (λ mem → <⇒≢ ((less-trans b<y (RBMember-All all[r]>y mem))) ∘ sym , right (right mem))
                      (elem-RBMember r))
  delformLeft-RBMember {A = A} proj b l@(node (black , _) _ _) y r b<y all[l]<y all[r]>y ord[l] ord[r] =
    balleft-All {A = A}
                 {P = (λ p → (proj p ≢ b) × Either (p ≡ y) (Either (RBMember p l) (RBMember p r))) }
                 y (del proj b l) r
                 ((<⇒≢ b<y) ∘ sym , left refl)
                 (mapAll (λ {(a≢b , mem) → a≢b , right (left mem)}) (del-RBMember proj b l ord[l]))
                 (mapAll (λ mem → <⇒≢ ((less-trans b<y (RBMember-All all[r]>y mem))) ∘ sym , right (right mem))
                         (elem-RBMember r))
  delformLeft-RBMember proj b l@(node (red , _) _ _) y r b<y all[l]<y all[r]>y ord[l] ord[r] =
    node (<⇒≢ b<y ∘ sym , left refl)
         (mapAll (λ {(a≢b , mem) → a≢b , right (left mem)}) (del-RBMember proj b l ord[l]))
         (mapAll (λ mem → <⇒≢ ((less-trans b<y (RBMember-All all[r]>y mem))) ∘ sym , right (right mem))
                         (elem-RBMember r))

  delformRight-RBMember :
    {{_ : Ord/Laws B}}
    → (proj : A → B)
    → (b : B)
    → (l : RedBlackTree A) → (y : A) → (r : RedBlackTree A)
    → (b > proj y)
    → All (λ p → proj (snd p)  < proj y) l → All (λ p → proj y < proj (snd p)) r
    → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) l
    → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) r
    → All (λ p → proj (snd p) ≢ b
               × Either ((snd p) ≡ y)
                (Either (RBMember (snd p) l)
                        (RBMember (snd p) r)))
          (delformRight proj b l y r)
  delformRight-RBMember proj b l y leaf b>y all[l]<y all[r]>y ord[l] ord[r] =
      node (<⇒≢ b>y , left refl)
           (mapAll (λ mem → <⇒≢ ((less-trans (RBMember-All all[l]<y mem) b>y)) , right (left mem))
                   (elem-RBMember l))
           leaf
  delformRight-RBMember proj b l y r@(node (red , _) _ _) b>y all[l]<y all[r]>y ord[l] ord[r] =
    node (<⇒≢ b>y , left refl)
         (mapAll (λ mem → <⇒≢ ((less-trans (RBMember-All all[l]<y mem) b>y)) , right (left mem))
                         (elem-RBMember l))
         (mapAll (λ {(a≢b , mem) → a≢b , right (right mem)}) (del-RBMember proj b r ord[r]))
  delformRight-RBMember {A = A} proj b l y r@(node (black , _) _ _) b>y all[l]<y all[r]>y ord[l] ord[r] =
    balright-All {A = A}
                 {P = (λ p → (proj p ≢ b) × Either (p ≡ y) (Either (RBMember p l) (RBMember p r))) }
                 y l (del proj b r)
                 ((<⇒≢ b>y) , left refl)
                 (mapAll (λ mem → <⇒≢ ((less-trans (RBMember-All all[l]<y mem) b>y)) , right (left mem))
                         (elem-RBMember l))
                 (mapAll (λ { (a≢b , mem) → a≢b , right (right mem)}) (del-RBMember proj b r ord[r]))


  del-RBMember :
    {{_ : Ord/Laws B}}
    → (proj : A → B)
    → (b : B)
    → (t : RedBlackTree A)
    → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) t
    → All (λ p → proj (snd p) ≢ b × RBMember (snd p) t) (del proj b t)
  del-RBMember proj b leaf ord[t] = leaf
  del-RBMember proj b (node (color , y) l r) (node (all[l]<y , all[r]>y) ord[l] ord[r])
    with compare b (proj y)
  ... | less lt =
      mapAll (λ { (a≢b , left a≡y) → a≢b , here (sym a≡y)
                ; (a≢b , right (left inl)) → a≢b , inLeft inl
                ; (a≢b , right (right inr)) → a≢b , inRight inr
                })
             (delformLeft-RBMember proj b l y r lt all[l]<y all[r]>y ord[l] ord[r])
  ... | greater gt =
      mapAll (λ { (a≢b , left a≡y) → a≢b , here (sym a≡y)
                ; (a≢b , right (left inl)) → a≢b , inLeft inl
                ; (a≢b , right (right inr)) → a≢b , inRight inr
                })
             (delformRight-RBMember proj b l y r gt all[l]<y all[r]>y ord[l] ord[r])
  ... | equal b≡p[y] =
        flip mapAll all-mem
          (λ { (left mem) →
                (λ a≡b → less-antirefl
                            (transport (_< proj y)
                                       (trans a≡b b≡p[y])
                                       (Member-All (snd (RBMember⇒Member mem)) all[l]<y)))
                 , inLeft mem
             ; (right mem) →
                 (λ a≡b → less-antirefl (transport (proj y <_)
                                        (trans a≡b b≡p[y])
                                        (Member-All (snd (RBMember⇒Member mem)) all[r]>y)))
                 , inRight mem
             })
       where
         all-mem : All (λ a → Either (RBMember (snd a) l) (RBMember (snd a) r)) (app l r)
         all-mem = app-All l r
                      ((mapAll left (elem-RBMember l)))
                      ((mapAll right (elem-RBMember r)))


deleteProj-RBMember :
  {{_ : Ord/Laws B}}
  → (proj : A → B)
  → (b : B)
  → (t : RedBlackTree A)
  → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) t
  → All (λ p → proj (snd p) ≢ b × RBMember (snd p) t) (deleteProj proj b t)
deleteProj-RBMember proj b t ord[t]
  with del proj b t | del-RBMember proj b t ord[t]
... | leaf | p@leaf = leaf
... | node (_ , z) l r | node x₂ p p₁ = node x₂ p p₁


DeleteEffectFst⇒¬RBProjMember :
  {{_ : Ord/Laws B}}
  → (proj : A → B)
  → (x : A)
  → (t : RedBlackTree A)
  → All (λ p → proj (snd p) ≢ proj x) t
  → ¬ RBProjMember proj (proj x) t
DeleteEffectFst⇒¬RBProjMember proj x .leaf leaf = λ ()
DeleteEffectFst⇒¬RBProjMember proj x (node (_ , y) l r) (node y≢x all[l] all[r])
 pmem
  with pmem
... | here x≡y = y≢x x≡y
... | inLeft inl =
  DeleteEffectFst⇒¬RBProjMember proj x l all[l] inl
... | inRight inr =
  DeleteEffectFst⇒¬RBProjMember proj x r all[r] inr


DeleteEffect⇒¬RBProjMember :
  {{_ : Ord/Laws B}}
  → (proj : A → B)
  → (x : A)
  → {t' : RB A}
  → (t : RedBlackTree A)
  → All (λ p → proj (snd p) ≢ proj x × RBMember (snd p) t') t
  → ¬ RBProjMember proj (proj x) t
DeleteEffect⇒¬RBProjMember proj x t all =
  DeleteEffectFst⇒¬RBProjMember proj x t (mapAll (λ p → fst p) all)



mutual

  delformLeft-Keeps-Unrelated :
    {{_ : Ord/Laws B}}
    → (proj : A → B)
    → (b : B)
    → (l : RedBlackTree A) → (y : A) → (r : RedBlackTree A)
    → (b < proj y)
    → All (λ p → proj (snd p)  < proj y) l → All (λ p → proj y < proj (snd p)) r
    → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) l
    → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) r
    → (a : A)
    → Either (y ≡ a) (Either (RBMember a l) (RBMember a r))
    → proj a ≢ b
    → RBMember a (delformLeft proj b l y r)
  delformLeft-Keeps-Unrelated proj b leaf y r b<y all[l]<y all[r]>y ord[l] ord[r] a mem a≢b =
    case mem of
      λ { (left x) → here x ; (right (right x)) → inRight x }
  delformLeft-Keeps-Unrelated {A = A} proj b l@(node (black , _) _ _) y r b<y all[l]<y all[r]>y ord[l] ord[r] a mem a≢b =
    balleft-Any y (del proj b l) r
      (case mem of
        λ { (left x) → left x
          ; (right (left inl)) → right (left (del-Keeps-Unrelated proj b l ord[l] a inl a≢b))
          ; (right (right inr)) → right (right inr)
          })
  delformLeft-Keeps-Unrelated proj b l@(node (red , _) _ _) y r b<y all[l]<y all[r]>y ord[l] ord[r] a mem a≢b =
    case mem of
      λ { (left x) → here x
        ; (right (left inl)) → inLeft (del-Keeps-Unrelated proj b l ord[l] a inl a≢b)
        ; (right (right inr)) → inRight inr
        }

  delformRight-Keeps-Unrelated :
    {{_ : Ord/Laws B}}
    → (proj : A → B)
    → (b : B)
    → (l : RedBlackTree A) → (y : A) → (r : RedBlackTree A)
    → (b > proj y)
    → All (λ p → proj (snd p)  < proj y) l → All (λ p → proj y < proj (snd p)) r
    → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) l
    → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) r
    → (a : A)
    → Either (y ≡ a) (Either (RBMember a l) (RBMember a r))
    → proj a ≢ b
    → RBMember a (delformRight proj b l y r)
  delformRight-Keeps-Unrelated proj b l y leaf b>y all[l]<y all[r]>y ord[l] ord[r] a mem a≢b =
    case mem of
      λ { (left x) → here x ; (right (left x)) → inLeft x }
  delformRight-Keeps-Unrelated proj b l y r@(node (red , _) _ _) b>y all[l]<y all[r]>y ord[l] ord[r] a mem a≢b =
    case mem of
      λ { (left x) → here x
        ; (right (left x)) → inLeft x
        ; (right (right x)) → inRight (del-Keeps-Unrelated proj b r ord[r] a x a≢b) }
  delformRight-Keeps-Unrelated {A = A} proj b l y r@(node (black , _) _ _) b>y all[l]<y all[r]>y ord[l] ord[r] a mem a≢b =
     balright-Any y l (del proj b r)
      (case mem of
        λ { (left x) → left x
          ; (right (left inl)) → right (left inl)
          ; (right (right inr)) → right (right (del-Keeps-Unrelated proj b r ord[r] a inr a≢b))
          })

  del-Keeps-Unrelated :
    {{_ : Ord/Laws B}}
    → (proj : A → B)
    → (b : B)
    → (t : RedBlackTree A)
    → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) t
    → (a : A)
    → (RBMember a t)
    → proj a ≢ b
    → RBMember a (del proj b t)
  del-Keeps-Unrelated proj b leaf ord[t] = λ a x x₁ → x
  del-Keeps-Unrelated proj b (node (color , y) l r) (node (all[l]<y , all[r]>y) ord[l] ord[r]) a mem a≢b
    with compare b (proj y)
  ... | less lt =
    delformLeft-Keeps-Unrelated
        proj b l y r lt
        all[l]<y all[r]>y
        ord[l] ord[r]
        a
        (case mem of λ { (here x) → left x ; (inLeft c) → right (left c) ; (inRight c) → right (right c)})
        a≢b
  ... | greater gt =
    delformRight-Keeps-Unrelated
        proj b l y r gt
        all[l]<y all[r]>y
        ord[l] ord[r]
        a
        (case mem of λ { (here x) → left x ; (inLeft c) → right (left c) ; (inRight c) → right (right c)})
        a≢b
  ... | equal b≡p[y] =
      case mem of
        λ { (here refl) → ⊥-elim (a≢b (sym b≡p[y]))
          ; (inLeft c) → app-Any l r (left c)
          ; (inRight c) → app-Any l r (right c)
          }

deleteProj-Keeps-Unrelated :
    {{_ : Ord/Laws B}}
    → (proj : A → B)
    → (b : B)
    → (t : RedBlackTree A)
    → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) t
    → (a : A)
    → (RBMember a t)
    → proj a ≢ b
    → RBMember a (deleteProj proj b t)
deleteProj-Keeps-Unrelated proj b t ord[t] a mem a≢b
  with del proj b t | del-Keeps-Unrelated proj b t ord[t] a mem a≢b
... | node (_ , y) l r | here y≡a = here y≡a
... | node (_ , y) l r | inLeft inl = inLeft inl
... | node (_ , y) l r | inRight inr = inRight inr