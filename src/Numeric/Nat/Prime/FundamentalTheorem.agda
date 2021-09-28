module Numeric.Nat.Prime.FundamentalTheorem where

open import Prelude
open import Control.WellFounded

open import Prelude.List.Relations.Any
open import Prelude.List.Relations.All
open import Prelude.List.Relations.Permutation
open import Prelude.List.Relations.Properties

open import Prelude.List.Properties
open import Numeric.Nat
open import Tactic.Nat

--- Some lemmas ----------

private
  primeProd=1-is-empty : ∀ ps → All Prime ps → productR ps ≡ 1 → ps ≡ []
  primeProd=1-is-empty [] _ _ = refl
  primeProd=1-is-empty (p ∷ ps) (prime p>1 _ ∷ _) pps=1 =
    let p=1 : p ≡ 1
        p=1 = mul=1-l p (productR ps) pps=1
    in case p=1 of λ where refl → refute p>1

  0<1<2 : ∀ {n} ⦃ _ : NonZero n ⦄ → n < 2 → n ≡ 1
  0<1<2 {0} ⦃ () ⦄ n<2
  0<1<2 {1} n<2 = refl
  0<1<2 {suc (suc _)} n<2 = refute n<2

  1>0 : ∀ {n} → n > 1 → NonZero n
  1>0 {0} n>1 = refute n>1
  1>0 {suc _} _ = _

  product-deleteIx : ∀ {a} ⦃ _ : NonZero a ⦄ (as : List Nat) (i : a ∈ as) →
                       productR as ≡ a * productR (deleteIx as i)
  product-deleteIx (a ∷ as) zero!   = refl
  product-deleteIx {a} (b ∷ as) (suc i) =
    b * productR as                  ≡⟨ b *_ $≡ product-deleteIx as i  ⟩
    b * productR (a ∷ deleteIx as i) ≡⟨ auto ⟩
    a * productR (b ∷ deleteIx as i) ∎

--- Factorisation ---------

record Factorisation (n : Nat) : Set where
  no-eta-equality
  constructor mkFactors
  pattern
  field
    factors       : List Nat
    factors-prime : All Prime factors
    factors-sound : productR factors ≡ n

open Factorisation

mul-factors : ∀ {a b} → Factorisation a → Factorisation b → Factorisation (a * b)
mul-factors {a} {b} (mkFactors ps psP ps=a) (mkFactors qs qsP qs=b) =
  mkFactors (ps ++ qs) (psP ++All qsP) $
    productR (ps ++ qs)       ≡⟨ product-++ ps _ ⟩
    productR ps * productR qs ≡⟨ _*_ $≡ ps=a *≡ qs=b ⟩
    a * b ∎

private
  factorise′ : ∀ n ⦃ _ : NonZero n ⦄ → Acc _<_ n → Factorisation n
  factorise′ n (acc wf) =
    case isPrime n of λ where
      (yes p) → mkFactors (n ∷ []) (p ∷ []) auto
      (no (composite a b a>1 b>1 refl)) →
        let instance _ = 1>0 a>1; _ = 1>0 b>1 in
        mul-factors (factorise′ a (wf a (less-mul-l a>1 b>1)))
                    (factorise′ b (wf b (less-mul-r a>1 b>1)))
      (tiny n<2) → mkFactors [] [] (sym (0<1<2 n<2))

  find-prime : ∀ p ps → Prime p → All Prime ps → p Divides productR ps → p ∈ ps
  find-prime p [] isP isPs p|1 = ⊥-elim (prime-divide-coprime p 1 1 isP refl p|1 p|1)
  find-prime p (q ∷ qs) isP (qP ∷ isPs) p|qqs =
    case prime-split q (productR qs) isP p|qqs of λ where
      (left  p|q)  → zero (prime-divide-prime isP qP p|q)
      (right p|qs) → suc  (find-prime p qs isP isPs p|qs)

  unique : (ps qs : List Nat) → All Prime ps → All Prime qs → productR ps ≡ productR qs → Permutation ps qs
  unique [] qs ips iqs ps=qs = case primeProd=1-is-empty qs iqs (sym ps=qs) of λ where refl → []
  unique (p ∷ ps) qs (pP ∷ psP) qsP pps=qs =
    let instance _ = prime-nonzero pP
        p|qs : p Divides productR qs
        p|qs = factor (productR ps) (by pps=qs)
        i : p ∈ qs
        i = find-prime p qs pP qsP p|qs
        ps=qs/p : productR ps ≡ productR (deleteIx qs i)
        ps=qs/p = mul-inj₂ p _ _ (pps=qs ⟨≡⟩ product-deleteIx qs i )
    in i ∷ unique ps (deleteIx qs i) psP (deleteAllIx qsP i) ps=qs/p

--- The Fundamental Theorem of arithmetic:
--    any nonzero natural number can be factored into a product of primes,
--    and the factorisation is unique up to permutation.

factorise : (n : Nat) ⦃ _ : NonZero n ⦄ → Factorisation n
factorise n = factorise′ n (wfNat n)

factors-unique : ∀ {n} (f₁ f₂ : Factorisation n) → Permutation (factors f₁) (factors f₂)
factors-unique (mkFactors ps psP ps=n) (mkFactors qs qsP qs=n) =
  unique ps qs psP qsP (ps=n ⟨≡⟩ʳ qs=n)
