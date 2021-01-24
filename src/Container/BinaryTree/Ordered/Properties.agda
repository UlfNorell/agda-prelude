module Container.BinaryTree.Ordered.Properties where


open import Container.BinaryTree.Base
open import Container.BinaryTree.Ordered
open import Container.BinaryTree.Relations

open import Prelude.Empty
open import Prelude.Ord
open import Prelude.Product
open import Prelude.Function
open import Prelude.Equality
open import Prelude.Equality.Inspect
open import Prelude.Maybe
open import Prelude.Sum
open import Prelude.Unit
open import Prelude.Variables

binarySearchBy-IsJust :
  {{_ : Ord B}}
  → (proj : A → B)
  → (b : B)
  → (t : BinaryTree A)
  → IsJust (binarySearchBy proj b t)
  → ProjMember proj b t
binarySearchBy-IsJust proj b (node x l r) bs
  with compare b (proj x)
... | less lt = inLeft (binarySearchBy-IsJust proj b l bs)
... | equal eq rewrite eq = here refl
... | greater gt = inRight (binarySearchBy-IsJust proj b r bs)

binarySearchBy-Nothing :
  {{_ : Ord/Laws B}}
  → (proj : A → B)
  → (b : B)
  → (t : BinaryTree A)
  → OrderedBy (λ p₁ p₂ → proj p₁ < proj p₂) t
  → binarySearchBy proj b t ≡ nothing
  → ¬ ProjMember proj b t
binarySearchBy-Nothing proj b (node x l r) (node (all[l]<x , all[r]>x) ord[l] ord[r]) bs
  with compare b (proj x)
... | less lt =
  case inspect (binarySearchBy proj b l) of
    λ { (just x with≡ eq) _ → case trans (sym eq) bs of λ ()
      ; (nothing with≡ eq) in[t] →
             case in[t] of
                λ { (here refl) → less-antirefl lt
                  ; (inLeft inl) → binarySearchBy-Nothing proj b l ord[l] bs inl
                  ; (inRight inr) → less-antirefl (less-trans (ProjMember-All {P = λ b → b > proj x} proj inr all[r]>x) lt) }
      }
... | equal eq rewrite eq = case bs of λ ()
... | greater gt =
  case inspect (binarySearchBy proj b r) of
    λ { (just x with≡ eq) _ → case trans (sym eq) bs of λ ()
      ; (nothing with≡ eq) in[t] →
             case in[t] of
                λ { (here refl) → less-antirefl gt
                  ; (inLeft inl) → less-antirefl (less-trans gt (ProjMember-All {P = λ b → b < proj x} proj inl all[l]<x))
                  ; (inRight inr) → binarySearchBy-Nothing proj b r ord[r] bs inr
                  }
      }

binarySearchBy-ProjMember :
  {{_ : Ord/Laws B}}
  → (proj : A → B)
  → (b : B)
  → (t : BinaryTree A)
  → ProjMember proj b t
  → OrderedBy (λ p₁ p₂ → proj p₁ < proj p₂) t
  → Σ A (λ a → binarySearchBy proj b t ≡ just a × proj a ≡ b × Member a t)
binarySearchBy-ProjMember proj b leaf () ord
binarySearchBy-ProjMember proj b (node x t t₁) (here refl) (node x₂ ord ord₁)
  with compare b (proj x)
... | less lt = ⊥-elim (less-antirefl lt)
... | equal eq = x , (refl , refl , here refl)
... | greater gt = ⊥-elim (less-antirefl gt)
binarySearchBy-ProjMember proj b (node x l r) (inLeft projmem) (node (all[l]<x , all[r]>x) ord[l] ord[r])
  with compare b (proj x)
... | less lt = let (a' , bs≡ , proja≡b , mem[a]t)  = binarySearchBy-ProjMember proj b l projmem ord[l]
                in (a' , bs≡ , proja≡b , inLeft mem[a]t)
... | equal eq rewrite eq = x , refl , refl , here refl
... | greater gt = ⊥-elim (less-antirefl (less-trans gt (ProjMember-All {P = λ b → b < proj x} proj projmem all[l]<x)))
binarySearchBy-ProjMember proj b (node x l r) (inRight projmem) (node (all[l]<x , all[r]>x) ord[l] ord[r])
  with compare b (proj x)
... | less lt = ⊥-elim (less-antirefl (less-trans (ProjMember-All {P = λ b → b > proj x} proj  projmem all[r]>x) lt))
... | equal eq rewrite eq = x , refl , refl , here refl
... | greater gt = let (a' , bs≡ ,  proja≡b , mem[a]t) =  binarySearchBy-ProjMember proj b r projmem ord[r]
                   in (a' , bs≡ , proja≡b , inRight mem[a]t)

binarySearchBy-¬ProjMember :
  {{_ : Ord B}}
  → (proj : A → B)
  → (b : B)
  → (t : BinaryTree A)
  → ¬ (ProjMember proj b t)
  → binarySearchBy proj b t ≡ nothing
binarySearchBy-¬ProjMember proj b leaf ¬member = refl
binarySearchBy-¬ProjMember proj b (node x l r) ¬member
  with compare b (proj x)
... | less lt = binarySearchBy-¬ProjMember proj b l (λ x₁ → ¬member (inLeft x₁))
... | equal refl = ⊥-elim (¬member (here refl))
... | greater gt = binarySearchBy-¬ProjMember proj b r (λ x₁ → ¬member (inRight x₁))

binarySearch-cases :
  {{_ : Ord/Laws B}}
  → (proj : A → B)
  → (b : B)
  → (t : BinaryTree A)
  → OrderedBy (λ p₁ p₂ → proj p₁ < proj p₂) t
  → Either (Σ A (λ a → binarySearchBy proj b t ≡ just a
                      × proj a ≡ b
                      × Member a t))
           (binarySearchBy proj b t ≡ nothing  × ¬ ProjMember proj b t)
binarySearch-cases proj b t ord[t]
  with inspect (binarySearchBy proj b t)
...| just a with≡ bs≡ =
  let projmem = binarySearchBy-IsJust proj b t (transport IsJust (sym bs≡) unit)
      (a' , bs≡' , proja≡b , mem[a]t) = binarySearchBy-ProjMember proj b t projmem ord[t]
  in left (a' , (bs≡' , (proja≡b , mem[a]t)))
...| nothing with≡ bs≡ =
  right (bs≡ , binarySearchBy-Nothing proj b t ord[t] bs≡)

binarySearchBy-ProjProjMember :
  {{_ : Ord/Laws C}}
  → (proj₁ : A → B)
  → (proj₂ : B → C)
  → (b : B)
  → (t : BinaryTree A)
  → ProjMember proj₁ b t
  → OrderedBy (λ p₁ p₂ → (proj₂ ∘ proj₁) p₁ < (proj₂ ∘ proj₁) p₂) t
  → Σ A (λ a → binarySearchBy (proj₂ ∘ proj₁) (proj₂ b) t ≡ just a × proj₁ a ≡ b)
binarySearchBy-ProjProjMember p₁ p₂ b leaf () ord[t]
binarySearchBy-ProjProjMember p₁ p₂ b (node x l r) (here px≡pb) (node (all[l]<x , all[r]>x) ord[l] ord[r])
  with compare (p₂ b) ((p₂ ∘ p₁) x)
... | less lt rewrite px≡pb = ⊥-elim (less-antirefl lt)
... | equal eq = x , (refl , px≡pb)
... | greater gt rewrite px≡pb = ⊥-elim (less-antirefl gt)
binarySearchBy-ProjProjMember p₁ p₂ b (node x l r) (inLeft mem) (node (all[l]<x , all[r]>x) ord[l] ord[r])
  with compare (p₂ b) ((p₂ ∘ p₁) x)
... | less lt = binarySearchBy-ProjProjMember p₁ p₂ b l mem ord[l]
... | equal eq = ⊥-elim (less-antirefl (transport (_< p₂ (p₁ x)) eq (ProjMember-All {P = (λ a → a < ((p₂ ∘ p₁) x))} (p₂ ∘ p₁) (mapAny (λ foo → cong p₂ foo) mem) all[l]<x)))
... | greater gt = ⊥-elim (less-antirefl (less-trans gt (ProjMember-All {P = (λ a → a < ((p₂ ∘ p₁) x))} (p₂ ∘ p₁) (mapAny (λ foo → cong p₂ foo) mem) all[l]<x)))
binarySearchBy-ProjProjMember p₁ p₂ b (node x l r) (inRight mem) (node (all[l]<x , all[r]>x) ord[l] ord[r])
  with compare (p₂ b) ((p₂ ∘ p₁) x)
... | less lt = ⊥-elim (less-antirefl (less-trans (ProjMember-All {P = (λ a → a > ((p₂ ∘ p₁) x))} (p₂ ∘ p₁) (mapAny (λ foo → cong p₂ foo) mem) all[r]>x) lt))
... | equal eq = ⊥-elim (less-antirefl (transport (p₂ (p₁ x) <_) eq (ProjMember-All {P = (λ a → a > ((p₂ ∘ p₁) x))} (p₂ ∘ p₁) (mapAny (λ foo → cong p₂ foo) mem) all[r]>x)))
... | greater gt = binarySearchBy-ProjProjMember p₁ p₂ b r mem ord[r]
