
module Tactic.Nat.Cong where

open import Prelude
open import Prelude.Equality.Unsafe using (safeEqual)
open import Builtin.Reflection
open import Tactic.Reflection.Quote

open import Tactic.Nat.Reflect
open import Tactic.Nat.Exp
open import Tactic.Nat.NF
open import Tactic.Nat.Simpl.Lemmas
open import Tactic.Nat.Auto.Lemmas

open import EqReasoning

simpl-sound : ∀ e ρ → ⟦ norm e ⟧ns ρ ≡ ⟦ e ⟧e ρ
simpl-sound e ρ = safeEqual $
  ⟦ norm e ⟧ns ρ
    ≡⟨ ns-sound (norm e) ρ ⟩
  ⟦ norm e ⟧n ρ
    ≡⟨ sound e ρ ⟩ʳ
  ⟦ e ⟧e ρ ∎

data All₂ {A B : Set} (P : A → B → Set) : List A → List B → Set where
  []  : All₂ P [] []
  _∷_ : ∀ {x y xs ys} → P x y → All₂ P xs ys → All₂ P (x ∷ xs) (y ∷ ys)

pattern _`∷₂_ x xs = con (quote All₂._∷_) (vArg x ∷ vArg xs ∷ [])
pattern `[]₂       = con (quote All₂.[]) []

envEq : {env₁ env₂ : List Nat} → All₂ _≡_ env₁ env₂ → env₁ ≡ env₂
envEq [] = refl
envEq (refl ∷ eqs) = cong _ (envEq eqs)

simpl-sound′ : ∀ e {env₁ env₂} → All₂ _≡_ env₁ env₂ → ⟦ norm e ⟧ns (buildEnv env₁) ≡ ⟦ e ⟧e (buildEnv env₂)
simpl-sound′ e eqs with envEq eqs
... | refl = simpl-sound e _

data CType : Set where
  tEq tAny : CType

data CTerm : CType → Set where
  cGoal  : CTerm tAny
  cRefl  : Term → CTerm tEq
  cSubst : ∀ {t} → Term → CTerm tEq → CTerm t → CTerm t
  cSimpl : Exp → List (CTerm tEq) → CTerm tEq

nth : ∀ {a} {A : Set a} → List A → Nat → A → A
nth []        n      z = z
nth (x ∷ xs)  zero   z = x
nth (x ∷ xs) (suc n) z = nth xs n z

impossible : Term
impossible = def (quote impossible) []

expToTerm : Exp → List Term → Term
expToTerm (var x)   env = nth env x impossible
expToTerm (lit n)   env = ` n
expToTerm (e ⟨+⟩ e₁) env = expToTerm e env `+ expToTerm e₁ env
expToTerm (e ⟨*⟩ e₁) env = expToTerm e env `* expToTerm e₁ env

-- What terms are an equality proving things about?
-- Not the right representation!
cEqTerms : CTerm tEq → Term × Term
cEqTerms (cRefl x) = x , x
cEqTerms (cSubst f eq c) = {!!}
cEqTerms (cSimpl e eqs) = {!!}

crefl : ∀ {a} {A : Set a} (x : A) → x ≡ x
crefl _ = refl

pattern `refl x       = def (quote crefl) (vArg x ∷ [])
pattern `subst f eq p = def (quote subst) (vArg f ∷ vArg eq ∷ vArg p ∷ [])
pattern `simpl e eqs  = def (quote simpl-sound′) (vArg e ∷ vArg eqs ∷ [])

fromCTerms : Term → List (CTerm tEq) → Term

fromCTerm′ : ∀ {t} → Term → CTerm t → Term
fromCTerm′ g cGoal           = g
fromCTerm′ g (cRefl x)       = `refl  (raise 1 $ stripImplicit x)
fromCTerm′ g (cSubst f eq c) = `subst (raise 1 $ stripImplicit f) (fromCTerm′ g eq) (fromCTerm′ g c)
fromCTerm′ g (cSimpl e eqs)  = `simpl (` e) (fromCTerms g eqs)

fromCTerms g []       = `[]₂
fromCTerms g (c ∷ cs) = fromCTerm′ g c `∷₂ fromCTerms g cs 

fromCTerm : ∀ {t} → CTerm t → Term
fromCTerm c = lam visible (fromCTerm′ (var 0 []) c)

data CExp : Set where
  cCxt  : Term → List (Exp × List CExp) → CExp
    -- cCxt C[x₁..xm] [ ei[y₁..yn] , [y₁↦c₁..yn↦cn] ]i

cexpToCTerm : ∀ t → CExp → CTerm t
cexpToCTerm tEq  (cCxt e []) = cRefl e
cexpToCTerm tAny (cCxt _ []) = cGoal
cexpToCTerm t (cCxt C ((e , cs) ∷ xs)) =
  cSubst (lam visible {!substitute!}) {!!} {!!}

-- It might help if I worked through a concrete example.

postulate
  f : Nat → Nat → Nat
  T : Nat → Nat → Set
  goal:_ : (A : Set) → A

ExType = ∀ n → T (f (n * 0) (n + 0) + 0) (n + 0)

ex : ExType
ex n =
  subst (λ x → T x (n + 0))
    (simpl-sound′ (var 0 ⟨+⟩ lit 0)
      (subst (λ x → f 0 n ≡ f x (n + 0))
          (simpl-sound′ (var 0 ⟨*⟩ lit 0) (crefl n ∷ []))
          (subst (λ x → f 0 n ≡ f 0 x)
            (simpl-sound′ (var 0 ⟨+⟩ lit 0) (crefl n ∷ [])) (crefl (f 0 n)))
        ∷ []))
    (subst (λ x → T (f 0 n) x)
      (simpl-sound′ (var 0 ⟨+⟩ lit 0) (crefl n ∷ []))
      {!!})

cterm : (n : Nat) → CTerm tAny
cterm n = cSubst (quoteTerm (λ x → T x (n + 0)))
          (cSimpl (var 0 ⟨+⟩ lit 0)
            ( cSubst (quoteTerm (λ x → f 0 n ≡ f x (n + 0)))
                     (cSimpl (var 0 ⟨*⟩ lit 0) (cRefl (quoteTerm n) ∷ []))
                     (cSubst (quoteTerm (λ x → f 0 n ≡ f 0 x))
                             (cSimpl (var 0 ⟨+⟩ lit 0) (cRefl (quoteTerm n) ∷ []))
                             (cRefl (quoteTerm (f 0 n))))
            ∷ []))
          (cSubst (quoteTerm (λ x → T (f 0 n) x))
                  (cSimpl (var 0 ⟨+⟩ lit 0) (cRefl (quoteTerm n) ∷ []))
                  cGoal)

pattern `T a b = def (quote T) (vArg a ∷ vArg b ∷ [])
pattern `f a b = def (quote f) (vArg a ∷ vArg b ∷ [])

cex-test : ExType
cex-test n = unquote (fromCTerm (cterm n)) {!!}

cexp : CExp
cexp = cCxt (`T (var 0 []) (var 1 []))
            ( ( var 0 ⟨+⟩ lit 0
              , cCxt (`f (var 0 []) (var 1 []))
                     ( (var 0 ⟨*⟩ lit 0 , cCxt (var 0 []) [] ∷ [])
                     ∷ (var 0 ⟨+⟩ lit 0 , cCxt (var 0 []) [] ∷ [])
                     ∷ [] )
                ∷ [] )
            ∷ (var 0 ⟨+⟩ lit 0 , cCxt (var 0 []) [] ∷ [])
            ∷ [] )

cexp-test : ExType
cexp-test n = quoteGoal g in {!cexpToCTerm tAny cexp!}

ex-test : ExType
ex-test n = quoteGoal g in {!g!}
