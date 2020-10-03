module Container.BinaryTree.RedBlack.Properties where

open import Container.BinaryTree.RedBlack

open import Container.BinaryTree.Base
import Container.BinaryTree.Ordered as Ord
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
open import Prelude.Variables

-- Special version of member for red-black trees

RBMember : A → RedBlackTree A → Set _
RBMember a t = Any ((a ≡_) ∘ snd) t

RBMember⇒Member : {a : A} {t : RedBlackTree A} → RBMember a t → Σ Color (λ c → Member (c , a) t)
RBMember⇒Member {a = x} {(node (color , y) _ _)} (here x≡y)
  rewrite x≡y = color , here refl
RBMember⇒Member {a = x} {(node _ l _) } (inLeft x∈l) =
  let (c , inL) = RBMember⇒Member x∈l
  in c , inLeft inL
RBMember⇒Member {a = x} {(node _ _ r)} (inRight x∈r) =
  let (c , inR) = RBMember⇒Member x∈r
  in c , inRight inR

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

leftBalance-ordered-ordered :
  {{_ : Ord/Laws B}}
  → {proj : A → B}
  → (color : Color)
  → (x : A) → (l : RedBlackTree A) → (r : RedBlackTree A)
  → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) l
  → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) r
  → All (λ p → proj (snd p)  < proj x) l → All (λ p → proj x < proj (snd p)) r
  → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) (leftBalance color x l r)
leftBalance-ordered-ordered color z l r ord[l] ord[r] all[l]<z all[r]>z
  with leftBalance-effect color z l r
... | left x₁ rewrite x₁ = node (all[l]<z , all[r]>z) ord[l] ord[r]
... | right ((x , y , a , b , c) , left refl , leftBalance≡) rewrite leftBalance≡ =
  case (ord[l] , all[l]<z) of
    λ { (node (node x<y all[a]<y all[b]>y , all[c]>y) (node (all[a]<x , all[b]>x) ord[lll] ord[llr]) ord[lr]
         , node y<z (node x<z all[a]<z all[b]<z) all[c]<z) →
           node ((node x<y all[a]<y all[b]>y)
                , (node y<z all[c]>y (mapAll (λ a z<a → less-trans y<z z<a) all[r]>z)))
                (node (all[a]<x , all[b]>x) ord[lll] ord[llr])
                (node (all[c]<z , all[r]>z) ord[lr] ord[r])
      }
... | right ((x , y , a , b , c) , right refl , leftBalance≡) rewrite leftBalance≡ =
  case (ord[l] , all[l]<z) of
    λ { (node (all[a]<x , node x<y all[b]>x all[c]>x) ord[a] (node (all[b]<y , all[c]>y) ord[b] ord[c])
        , node x<z all[l]<z (node y<z all[b]<z all[c]<z)) →
          node ((node x<y (mapAll (λ a a<x → less-trans a<x x<y) all[a]<x) all[b]<y)
               , (node y<z all[c]>y (mapAll (λ a z>a → less-trans y<z z>a) all[r]>z)))
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

rightBalance-ordered-ordered :
  {{_ : Ord/Laws B}}
  → {proj : A → B}
  → (color : Color)
  → (x : A) → (l : RedBlackTree A) → (r : RedBlackTree A)
  → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) l
  → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) r
  → All (λ p → proj (snd p)  < proj x) l → All (λ p → proj x < proj (snd p)) r
  → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) (rightBalance color x l r)
rightBalance-ordered-ordered color x l r ord[l] ord[r] all[l]<x all[r]>x
  with rightBalance-effect color x l r
... | left rightBalance≡ rewrite rightBalance≡ = node (all[l]<x , all[r]>x) ord[l] ord[r]
... | right ((z , y , a , b , c) , left refl , rightBalance≡) rewrite rightBalance≡ =
  case (ord[r] , all[r]>x) of
    λ { (node ((node z<y all[a]<y all[b]<y) , all[c]>y) (node (all[a]<z , all[b]>z) ord[a] ord[b]) ord[c]
        , node x<y (node x<z all[a]>x all[b]>x) all[c]>x) →
          node ((node x<z (mapAll (λ a a<x → less-trans a<x x<z) all[l]<x) all[a]<z)
               , (node z<y all[b]>z (mapAll (λ a a>y → less-trans z<y a>y ) all[c]>y)))
               (node (all[l]<x , all[a]>x) ord[l] ord[a])
               (node (all[b]<y , all[c]>y) ord[b] ord[c])
    }
... | right ((y , z , a , b , c) , right refl , rightBalance≡) rewrite rightBalance≡ =
   case (ord[r] , all[r]>x) of
     λ { (node (all[a]<y , node y<z all[b]>y all[c]>y) ord[a] (node (all[b]<z , all[c]>z) ord[b] ord[c])
         , node x<y all[r]>x (node x<z all[b]>x all[c]>x)) →
           node ((node x<y (mapAll (λ a a<x → less-trans a<x x<y) all[l]<x) all[a]<y)
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

insertInner-ordered-ordered :
  {{_ : Ord/Laws B}}
  → (proj : A → B)
  → (x : A)
  → (t : RedBlackTree A)
  → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) t
  → OrderedBy (λ p₁ p₂ → proj (snd p₁) < proj (snd p₂)) (insertInner proj (proj x) x t)
insertInner-ordered-ordered _ x leaf leaf =
  node (leaf , leaf) leaf leaf
insertInner-ordered-ordered
  proj x
  (node (color , y) l r)
  ord[t]@(node (all[l]<y , all[r]>y) ord[l] ord[r])
  with compare (proj x) (proj y)
...| equal x≡b =
  node (transport (λ z → All (λ x → proj (snd x) < z) l) (sym x≡b) all[l]<y
       , transport (λ z → All (λ x → z < proj (snd x)) r) (sym x≡b) all[r]>y) ord[l] ord[r]
...| greater y<x with insertInner proj (proj x) x r
                    | insertInner-ordered-ordered proj x r ord[r]
                    | insertInner-All proj x r y<x all[r]>y
... | leaf | leaf | _ = rightBalance-ordered-ordered color y l leaf ord[l] leaf all[l]<y leaf
... | r'@(node _ _ _) | ord[r']@(node _ _ _) | allP[insertInner] =
  rightBalance-ordered-ordered
    color y l r'
    ord[l] ord[r']
    all[l]<y allP[insertInner]
insertInner-ordered-ordered proj x (node (color , y) l r) ord[t]@(node (all[l]<y , all[r]>y) ord[l] ord[r])
  | less x<y with insertInner proj (proj x) x l
                | insertInner-ordered-ordered proj x l ord[l]
                | insertInner-All proj x l x<y all[l]<y
... | leaf | leaf | _ =
  leftBalance-ordered-ordered color y leaf r leaf ord[r] leaf all[r]>y
... | l'@(node _ _ _) | ord[l']@(node _ _ _) | allP[insertInner] =
  leftBalance-ordered-ordered
    color y l' r
    ord[l'] ord[r]
    allP[insertInner] all[r]>y

insertInner-Member :
    {{_ : Ord/Laws B}}
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


insertInner-keeps-Member :
    {{_ : Ord/Laws B}}
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

lookupBy-Member :
  {{OLB : Ord/Laws B}}
  → (proj : A → B)
  → (x : A)
  → (t : RedBlackTree A)
  → RBMember x t
  → OrderedBy (λ a b → proj (snd a) < proj (snd b)) t
  → lookupBy proj (proj x) t ≡ just x
lookupBy-Member proj x (node (_ , y) _ _) (here x≡y) ord[t] rewrite x≡y
  with compare (proj y) (proj y)
... | less lt = ⊥-elim (less-antirefl lt)
... | equal eq = refl
... | greater gt = ⊥-elim (less-antirefl gt)
lookupBy-Member proj x (node (_ , y) l r) (inLeft x∈l) (node (all[l]<y , _) ord[l] _)
  with compare (proj x) (proj y)
... | less lt = lookupBy-Member proj x l x∈l ord[l]
... | equal p[x]≡p[y] =
  ⊥-elim (less-antirefl
              (transport (λ z → z < proj y)
                         p[x]≡p[y]
                         (member-all all[l]<y (snd (RBMember⇒Member x∈l)))
              ))
... | greater p[y]<p[x] = ⊥-elim (<⇒≱ (member-all all[l]<y (snd (RBMember⇒Member x∈l)))
                                        (<⇒≤ p[y]<p[x]))
lookupBy-Member proj x (node (_ , y) l r) (inRight x∈r) (node (_ , all[r]>y) _ ord[r])
  with compare (proj x) (proj y)
... | less p[x]<p[y] =
 ⊥-elim (<⇒≱ (member-all all[r]>y (snd (RBMember⇒Member x∈r)))
               (<⇒≤ p[x]<p[y]))
... | equal p[x]≡p[y] =
  ⊥-elim (less-antirefl
              (transport (λ z → z > proj y)
                         p[x]≡p[y]
                         (member-all all[r]>y (snd (RBMember⇒Member x∈r)))
              ))
... | greater gt = lookupBy-Member proj x r x∈r ord[r]

-- binarySearchBy∘insertInner :
--   {{_ : Ord/Laws B}}
--   → (proj : A → B)
--   → (x : A)
--   → (t : RedBlackTree A)
--   → Σ Color (λ c → binarySearchBy (proj ∘ snd) (proj x) (insertInner proj (proj x) x t) ≡ just (c , x))
-- binarySearchBy∘insertInner proj x leaf
--   with compare (proj x) ((proj ∘ snd) (red , x))
-- ... | less lt = ⊥-elim (less-antirefl lt)
-- ... | equal refl = red , refl
-- ... | greater gt = ⊥-elim (less-antirefl gt)
-- binarySearchBy∘insertInner proj x (node (c , y) l r)
--   with compare (proj x) (proj y)
-- ... | less lt = {!!}
-- ... | greater gt = {!!}
-- ... | equal x≡y with compare (proj x) (proj x)
-- ... | less lt = ⊥-elim (less-antirefl lt)
-- ... | equal refl = c , cong (λ z → just (c , z)) refl
-- ... | greater gt = ⊥-elim (less-antirefl gt)
