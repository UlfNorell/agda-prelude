module Container.Dictionary.Properties where


open import Container.Dictionary
open import Container.BinaryTree.RedBlack
open import Container.BinaryTree.Relations
open import Container.BinaryTree.RedBlack.Properties

open import Prelude.Ord
open import Prelude.Function
open import Prelude.Product
open import Prelude.Maybe
open import Prelude.Sum
open import Prelude.Equality
open import Prelude.Empty
open import Prelude.Functor
open import Prelude.Variables

Associated : A → B → Dictionary A B → Set _
Associated k v d = RBMember (k , v) (Dictionary.unwrap d)

ContainsKey : A → Dictionary A B → Set _
ContainsKey k d = RBProjMember fst k (Dictionary.unwrap d)

WellFormed : {{_ : Ord/Laws A}} → Dictionary A B → Set _
WellFormed (record {unwrap = rb}) = OrderedBy (λ p₁ p₂ → fst (snd p₁) < fst (snd p₂)) rb


ContainsKey⇒Associated :
  {k : A} → {d : Dictionary A B}
  → ContainsKey k d
  → Σ B (λ v → Associated k v d)
ContainsKey⇒Associated contains
  with ProjMember⇒Member (fst ∘ snd) contains
...| (c , k' , v) , assoc , refl = v , mapAny (λ  x≡ → cong snd x≡) assoc


set-associated : {{_ : Ord A}} (k : A) (v : B) → (d : Dictionary A B)
               → Associated k v (set k v d)
set-associated k v d = insertBy-Member fst (k , v) (Dictionary.unwrap d)

set-keeps-associated : {{_ : Ord A}}
                     → (k : A) (v : B)
                     → {k' : A} {v' : B}
                     → {d : Dictionary A B}
                     → (k ≢ k')
                     → Associated k' v' d
                     → Associated k' v' (set k v d)
set-keeps-associated k v {k' = k'} {v' = v'} {d = d} k≢k' k'↦v' =
  insertBy-keeps-Member fst (k , v) (k' , v') (Dictionary.unwrap d) k≢k' k'↦v'

set-WellFormed :
  {{_ : Ord/Laws A}} (k : A) (v : B) → {d : Dictionary A B}
  → WellFormed d
  → WellFormed (set k v d)
set-WellFormed k v {d = d} wf = (insertBy-ordered fst (k , v) (Dictionary.unwrap d) wf)

get-Associcated :
  {{_ : Ord/Laws A}}
  → {k : A} → {v : B}
  → {d : Dictionary A B}
  → Associated k v d
  → WellFormed d
  → get k d ≡ just v
get-Associcated {k = k} {v = v} {d = (record { unwrap = t})} assoc wf
  with lookupBy fst k t | lookupBy-RBMember fst (k , v) t assoc wf
... | just .(k , v) | refl = refl
... | nothing | ()

get-ContaninsKey :
  {{_ : Ord/Laws A}}
  → {k : A}
  → {d : Dictionary A B}
  → ContainsKey k d
  → WellFormed d
  → Σ B (λ v → get k d ≡ just v)
get-ContaninsKey keymem wf
  with RBProjMember⇒RBMember keymem
...| (k' , v) , refl , rbmem = v , get-Associcated rbmem wf

get-¬ContainsKey :
  {{_ : Ord/Laws A}}
  → {k : A}
  → {d : Dictionary A B}
  → ¬ ContainsKey k d
  → get k d ≡ nothing
get-¬ContainsKey ¬containskey
  rewrite lookupBy-¬RBProjMember _ ¬containskey = refl

remove-¬ContainsKey :
  {{_ : Ord/Laws A}}
  → (k : A)
  → {d : Dictionary A B}
  → WellFormed d
  → ¬ ContainsKey k (remove k d)
remove-¬ContainsKey k {d = d} wf contains =
  All¬⇒¬Any (mapAll fst (deleteProj-RBMember fst k (Dictionary.unwrap d) wf)) contains

remove-Keeps-Associated :
  {{_ : Ord/Laws A}}
  → {k : A}
  → {k' : A}
  → {v : B}
  → {d : Dictionary A B}
  → Associated k' v d
  → WellFormed d
  → k ≢ k'
  → Associated k' v (remove k d)
remove-Keeps-Associated {k = k} {k' = k'} {v = v} {d = d} assoc wf k≢k' =
  deleteProj-Keeps-Unrelated fst k (Dictionary.unwrap d) wf (k' , v) assoc (≢-sym k≢k')

get∘set-same :
  {{_ : Ord/Laws A}}
  → {k : A} → {v : B}
  → {d : Dictionary A B}
  → WellFormed d
  → get k (set k v d) ≡ just v
get∘set-same {k = k} {v = v} {d = d} wf =
  get-Associcated (set-associated k v d) (set-WellFormed k v wf)

get∘set-diffrent-associated :
  {{_ : Ord/Laws A}}
  → (k : A) → (v : B)
  → {k' : A} → {v' : B}
  → {d : Dictionary A B}
  → WellFormed d
  → k ≢ k'
  → Associated k' v' d
  → get k' (set k v d) ≡ just v'
get∘set-diffrent-associated k v {k' = k'} {v' = v' } {d = d} wf k≢k' assoc =
  get-Associcated (set-keeps-associated k v k≢k' assoc ) (set-WellFormed k v wf)

get∘set-diffrent :
  {{_ : Ord/Laws A}}
  → (k : A) → (v : B)
  → (k' : A)
  → {d : Dictionary A B}
  → WellFormed d
  → k ≢ k'
  → get k' (set k v d) ≡ get k' d
get∘set-diffrent k v k' {d} wf k≢k'
  with lookupBy-cases fst k' wf
... | left ((_ , v'') , lookup≡ , mem , k''≡k')
  rewrite k''≡k' rewrite lookup≡ =
  cong (fmap′ snd)
       (lookupBy-RBMember fst (k' , v'') _ (insertBy-keeps-Member fst (k , v) (k' , v'') (Dictionary.unwrap d) k≢k'  mem)
                          (insertBy-ordered fst (k , v) _ wf))
... | right (lookup≡nothing , ¬mem) rewrite lookup≡nothing =
  {!lookupBy-¬RBProjMember fst ¬mem  !}

get∘remove-same :
  {{_ : Ord/Laws A}}
  → (k : A)
  → {d : Dictionary A B}
  → WellFormed d
  → get k (remove k d) ≡ nothing
get∘remove-same k {d = d } wf =
  get-¬ContainsKey (remove-¬ContainsKey k wf)
