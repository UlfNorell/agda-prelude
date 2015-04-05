
module Tactic.Nat.Subtract.Lemmas where

open import Prelude
open import Tactic.Nat.NF
open import Tactic.Nat.Exp
open import Data.Bag
open import Tactic.Nat.Simpl
open import Data.Nat.Properties.Core
open import Data.List.Properties
open import Tactic.Nat.Auto.Lemmas
open import Tactic.Nat.Simpl.Lemmas
open import Tactic.Nat.Auto
open import Tactic.Nat.Simpl

open import Tactic.Nat.Subtract.Exp

private
  sub-cancel : ∀ a → a - a ≡ 0
  sub-cancel zero = refl
  sub-cancel (suc a) = sub-cancel a

  sub-add-r : ∀ a b c → a - (b + c) ≡ a - b - c
  sub-add-r  a       zero    c      = refl
  sub-add-r zero    (suc b)  zero   = refl
  sub-add-r zero    (suc b) (suc c) = refl
  sub-add-r (suc a) (suc b)  c      = sub-add-r a b c

  lem-sub-zero : ∀ a b c → b + c ≡ a → c ≡ a - b
  lem-sub-zero ._  zero   c refl = refl
  lem-sub-zero ._ (suc b) c refl = lem-sub-zero _ b c refl

  lem-zero-sub : ∀ a b c → b ≡ a + c → 0 ≡ a - b
  lem-zero-sub  zero   ._  zero   refl = refl
  lem-zero-sub  zero   ._ (suc c) refl = refl
  lem-zero-sub (suc a) ._  c      refl = lem-zero-sub a _ c refl

  lem-sub : ∀ a b u v → b + u ≡ a + v → u - v ≡ a - b
  lem-sub  zero    zero   u ._ refl = sub-cancel u
  lem-sub  zero   (suc b) u ._ refl = sym $ lem-zero-sub u (suc b + u) (suc b) auto
  lem-sub (suc a)  zero  ._  v refl = sym $ lem-sub-zero (suc a + v) v (suc a) auto
  lem-sub (suc a) (suc b) u  v eq   = lem-sub a b u v (suc-inj eq)

  sub-mul-distr-l : ∀ a b c → (a - b) * c ≡ a * c - b * c
  sub-mul-distr-l zero b c = (_* c) $≡ lem-zero-sub 0 b b refl ʳ⟨≡⟩ lem-zero-sub 0 (b * c) (b * c) refl
  sub-mul-distr-l (suc a) zero c = refl
  sub-mul-distr-l (suc a) (suc b) c =
    sub-mul-distr-l a b c ⟨≡⟩
    lem-sub (suc a * c) (suc b * c) (a * c) (b * c) auto

  sub-mul-distr-r : ∀ a b c → a * (b - c) ≡ a * b - a * c
  sub-mul-distr-r a b c =
    auto ⟨≡⟩ sub-mul-distr-l b c a
         ⟨≡⟩ cong₂ _-_ (mul-commute b a) (mul-commute c a)

-- The evaluator that doesn't generate x * 1 + 0 is the same as the
-- one that does.

lem-simp-eval : ∀ n ρ → ⟦ n ⟧sns ρ ≡ ⟦ n ⟧sn ρ

private
  lem-simp-eval-t : ∀ t ρ → ⟦ t ⟧sts ρ ≡ ⟦ t ⟧st ρ
  lem-simp-eval-a : ∀ a ρ → ⟦ a ⟧sas ρ ≡ ⟦ a ⟧sa ρ

  lem-simp-eval-a (var x) ρ = refl
  lem-simp-eval-a (a ⟨-⟩ b) ρ = _-_ $≡ lem-simp-eval a ρ *≡ lem-simp-eval b ρ

  lem-simp-eval-t []          ρ = refl
  lem-simp-eval-t (x ∷ [])    ρ = lem-simp-eval-a x ρ ⟨≡⟩ auto
  lem-simp-eval-t (x ∷ y ∷ t) ρ = _*_ $≡ lem-simp-eval-a x ρ *≡ lem-simp-eval-t (y ∷ t) ρ

lem-simp-eval []                 ρ = refl
lem-simp-eval ((k , t) ∷ [])     ρ = _*_ k $≡ lem-simp-eval-t t ρ ⟨≡⟩ auto
lem-simp-eval ((k , t) ∷ t₁ ∷ n) ρ = _+_ $≡ (_*_ k $≡ lem-simp-eval-t t ρ)
                                         *≡ lem-simp-eval (t₁ ∷ n) ρ

-- The evaluation that the termination checker lets us write is the
-- same as the one we want to write.

private
  lem-sub-eval-t : ∀ t ρ → ⟦ t ⟧st ρ ≡ product (map (atomEnv ρ) t)
  lem-sub-eval-t [] ρ = refl
  lem-sub-eval-t (x ∷ t) ρ = (⟦ x ⟧sa ρ *_) $≡ lem-sub-eval-t t ρ

lem-sub-eval   : ∀ n ρ → ⟦ n ⟧sn ρ ≡ ⟦ n ⟧n (atomEnv ρ)
lem-sub-eval []            ρ = refl
lem-sub-eval ((k , t) ∷ n) ρ = _+_ $≡ (_*_ k $≡ lem-sub-eval-t t ρ) *≡ lem-sub-eval n ρ

private
  lem-env : ∀ ρ x → atomEnvS ρ x ≡ atomEnv ρ x
  lem-env ρ (var x) = refl
  lem-env ρ (a ⟨-⟩ b) = _-_ $≡ lem-simp-eval a ρ *≡ lem-simp-eval b ρ

-- Combining the above equalities.

lem-sub-eval-simp : ∀ n ρ → ⟦ n ⟧sn ρ ≡ ⟦ n ⟧n (atomEnvS ρ)
lem-sub-eval-simp n ρ = lem-sub-eval n ρ ⟨≡⟩ʳ lem-eval-env (atomEnvS ρ) (atomEnv ρ) (lem-env ρ) n

⟨-⟩-sound′ : ∀ a b ρ → ⟦ a -nf′ b ⟧n (atomEnv ρ) ≡ ⟦ a ⟧n (atomEnv ρ) - ⟦ b ⟧n (atomEnv ρ)
⟨-⟩-sound′ a b ρ with cancel a b | λ i j → cancel-complete′ i j a b (atomEnv ρ)
⟨-⟩-sound′ a b ρ | d      , []     | complete =
  let u = ⟦ a ⟧n (atomEnv ρ)
      v = ⟦ b ⟧n (atomEnv ρ)
      k = ⟦ d ⟧n (atomEnv ρ) in
  lem-sub-zero u v k (complete v u auto ⟨≡⟩ auto)
⟨-⟩-sound′ a b ρ | []     , d ∷ ds | complete =
  let u = ⟦ a      ⟧n (atomEnv ρ)
      v = ⟦ b      ⟧n (atomEnv ρ)
      k = ⟦ d ∷ ds ⟧n (atomEnv ρ) in
  lem-zero-sub u v k (auto ⟨≡⟩ complete v u auto)
⟨-⟩-sound′ a b ρ | u ∷ us , v ∷ vs | complete =
  let eval = λ x → ⟦ x ⟧n (atomEnv ρ) in
  auto ⟨≡⟩ cong₂ _-_ (lem-sub-eval (u ∷ us) ρ) (lem-sub-eval (v ∷ vs) ρ) ⟨≡⟩
  lem-sub (eval a) (eval b) (eval (u ∷ us)) (eval (v ∷ vs)) (complete (eval b) (eval a) auto)

⟨-⟩-sound : ∀ a b ρ → ⟦ a -nf b ⟧n (atomEnv ρ) ≡ ⟦ a ⟧n (atomEnv ρ) - ⟦ b ⟧n (atomEnv ρ)
⟨-⟩-sound a b ρ with is-subtraction a
⟨-⟩-sound a b ρ  | no     = ⟨-⟩-sound′ a b ρ
⟨-⟩-sound ._ c ρ | a ⟨-⟩ b =
  let eval = λ x → ⟦ x ⟧n (atomEnv ρ) in
  ⟨-⟩-sound′ a (b +nf c) ρ ⟨≡⟩
  (eval a -_) $≡ ⟨+⟩-sound b c (atomEnv ρ) ⟨≡⟩
  sub-add-r (eval a) (eval b) (eval c) ⟨≡⟩
  (_- eval c) $≡ (_-_ $≡ lem-sub-eval a ρ *≡ lem-sub-eval b ρ) ʳ⟨≡⟩
  (_- eval c) $≡ auto

⟨*⟩-sound′ : ∀ a b ρ → ⟦ a *nf′ b ⟧n (atomEnv ρ) ≡ ⟦ a ⟧n (atomEnv ρ) * ⟦ b ⟧n (atomEnv ρ)
⟨*⟩-sound′ a  b  ρ with is-subtraction a
⟨*⟩-sound′ ._ c  ρ | a ⟨-⟩ b =
  let eval x = ⟦ x ⟧n (atomEnv ρ) in
  ⟨-⟩-sound (a *nf′ c) (b *nf′ c) ρ ⟨≡⟩
  _-_ $≡ ⟨*⟩-sound′ a c ρ *≡ ⟨*⟩-sound′ b c ρ ⟨≡⟩
  sub-mul-distr-l (eval a) (eval b) (eval c) ʳ⟨≡⟩
  (_* eval c) $≡ (_-_ $≡ lem-sub-eval a ρ *≡ lem-sub-eval b ρ) ʳ⟨≡⟩
  auto
⟨*⟩-sound′ a  b  ρ | no with is-subtraction b
⟨*⟩-sound′ a  ._ ρ | no | b ⟨-⟩ c =
  let eval x = ⟦ x ⟧n (atomEnv ρ) in
  ⟨-⟩-sound (a *nf b) (a *nf′ c) ρ ⟨≡⟩
  _-_ $≡ ⟨*⟩-sound a b (atomEnv ρ) *≡ ⟨*⟩-sound′ a c ρ ⟨≡⟩
  sub-mul-distr-r (eval a) (eval b) (eval c) ʳ⟨≡⟩
  (eval a *_) $≡ (_-_ $≡ lem-sub-eval b ρ *≡ lem-sub-eval c ρ) ʳ⟨≡⟩
  auto
⟨*⟩-sound′ a  b  ρ | no | no = ⟨*⟩-sound a b (atomEnv ρ)

sound-sub : ∀ e ρ → ⟦ e ⟧se ρ ≡ ⟦ normSub e ⟧sn ρ
sound-sub (var x) ρ = auto
sound-sub (lit 0) ρ = refl
sound-sub (lit (suc n)) ρ = auto
sound-sub (e ⟨+⟩ e₁) ρ =
  cong₂ _+_ (sound-sub e  ρ ⟨≡⟩ lem-sub-eval (normSub e)  ρ)
            (sound-sub e₁ ρ ⟨≡⟩ lem-sub-eval (normSub e₁) ρ) ⟨≡⟩
  ⟨+⟩-sound (normSub e) (normSub e₁) (atomEnv ρ) ʳ⟨≡⟩ʳ
  lem-sub-eval (normSub (e ⟨+⟩ e₁)) ρ
sound-sub (e ⟨*⟩ e₁) ρ =
  cong₂ _*_ (sound-sub e  ρ ⟨≡⟩ lem-sub-eval (normSub e)  ρ)
            (sound-sub e₁ ρ ⟨≡⟩ lem-sub-eval (normSub e₁) ρ) ⟨≡⟩
  ⟨*⟩-sound′ (normSub e) (normSub e₁) ρ ʳ⟨≡⟩ʳ
  lem-sub-eval (normSub (e ⟨*⟩ e₁)) ρ
sound-sub (e ⟨-⟩ e₁) ρ =
  cong₂ _-_ (sound-sub e  ρ ⟨≡⟩ lem-sub-eval (normSub e)  ρ)
            (sound-sub e₁ ρ ⟨≡⟩ lem-sub-eval (normSub e₁) ρ) ⟨≡⟩
  ⟨-⟩-sound (normSub e) (normSub e₁) ρ ʳ⟨≡⟩ʳ
  lem-sub-eval (normSub (e ⟨-⟩ e₁)) ρ
