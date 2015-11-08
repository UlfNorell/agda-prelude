
module Tactic.Nat.Subtract.Refute where

open import Prelude
open import Builtin.Reflection
open import Tactic.Reflection.Quote
open import Tactic.Reflection
open import Control.Monad.State

open import Tactic.Nat.Reflect
open import Tactic.Nat.NF
open import Tactic.Nat.Exp
open import Tactic.Nat.Auto
open import Tactic.Nat.Auto.Lemmas
open import Tactic.Nat.Simpl.Lemmas
open import Tactic.Nat.Simpl
open import Tactic.Nat.Reflect

open import Tactic.Nat.Subtract.Exp
open import Tactic.Nat.Subtract.Reflect
open import Tactic.Nat.Subtract.Lemmas
open import Tactic.Nat.Less.Lemmas

data Impossible : Set where

invalidEquation : ⊤
invalidEquation = _

private
  0≠suc : ∀ n → 0 ≡ Nat.suc n → ⊥
  0≠suc n ()

  n≮0 : {n : Nat} → n < 0 → ⊥
  n≮0 (diff k ())

  lem-refute : ∀ n nf ρ → 0 ≡ ⟦ (suc n , []) ∷ nf ⟧ns (atomEnvS ρ) → ⊥
  lem-refute n nf ρ eq = erase-⊥ $ 0≠suc (n + ⟦ nf ⟧n (atomEnvS ρ)) $
    eq ⟨≡⟩ ns-sound ((suc n , []) ∷ nf) (atomEnvS ρ) ⟨≡⟩ auto

refutation-proof : ∀ {a} {A : Set a} eqn ρ → Maybe (⟦ eqn ⟧eqn ρ → A)
refutation-proof (a :≡ b) ρ with cancel (normSub a) (normSub b) | complicateSubEq a b ρ
refutation-proof (a :≡ b) ρ | [] , (suc n , []) ∷ v | compl = just λ eq → ⊥-elim $ lem-refute n v ρ (compl eq)
refutation-proof (a :≡ b) ρ | (suc n , []) ∷ v , [] | compl = just λ eq → ⊥-elim $ lem-refute n v ρ (sym (compl eq))
refutation-proof (a :≡ b) ρ | _ , _ | _ = nothing

refutation-proof (a :< b) ρ with cancel (normSub a) (normSub b) | complicateSubLess a b ρ
refutation-proof (a :< b) ρ | v , [] | compl = just λ eq → ⊥-elim $ erase-⊥ $ n≮0 (compl eq)
refutation-proof (a :< b) ρ | _ , _  | _     = nothing

-- Some trickery to make tactics call be erased
get-absurd-proof : ∀ {a} {A : Set a} (prf : Maybe (A → ⊥)) → QED {x = prf} → A → ⊥
get-absurd-proof = get-proof

get-refute-proof : ∀ {a b} {A : Set a} {B : Set b} (prf : Maybe (A → ⊥)) → QED {x = prf} → A → B
get-refute-proof eq x y = ⊥-elim (get-absurd-proof eq x y)
{-# INLINE get-refute-proof #-}

refutesub-tactic : Term → Term
refutesub-tactic (pi (vArg (el _ a)) _) =
  case termToSubEqn a of λ
  { nothing → failedProof (quote invalidEquation) a
  ; (just (eqn , Γ)) →
    getProof (quote cantProve) a $
    def (quote refutation-proof)
        $ vArg (` eqn)
        ∷ vArg (quotedEnv Γ)
        ∷ []
  }
refutesub-tactic _ = def (quote Impossible) []
