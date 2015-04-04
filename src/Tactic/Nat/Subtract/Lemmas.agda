
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

atomEnv : Env Var → Env SubAtom
atomEnv ρ x = ⟦ x ⟧sa ρ

lem-sub-eval-t : ∀ t ρ → ⟦ t ⟧st ρ ≡ product (map (atomEnv ρ) t)
lem-sub-eval-t [] ρ = refl
lem-sub-eval-t (x ∷ t) ρ = (⟦ x ⟧sa ρ *_) $≡ lem-sub-eval-t t ρ

lem-sub-eval   : ∀ n ρ → ⟦ n ⟧sn ρ ≡ ⟦ n ⟧n (atomEnv ρ)
lem-sub-eval []            ρ = refl
lem-sub-eval ((k , t) ∷ n) ρ = _+_ $≡ (_*_ k $≡ lem-sub-eval-t t ρ) *≡ lem-sub-eval n ρ

⟨-⟩-sound : ∀ a b ρ → ⟦ a -nf b ⟧n (atomEnv ρ) ≡ ⟦ a ⟧n (atomEnv ρ) - ⟦ b ⟧n (atomEnv ρ)
⟨-⟩-sound a b ρ with cancel a b | λ i j → cancel-complete′ i j a b (atomEnv ρ)
⟨-⟩-sound a b ρ | d      , []     | complete =
  let u = ⟦ a ⟧n (atomEnv ρ)
      v = ⟦ b ⟧n (atomEnv ρ)
      k = ⟦ d ⟧n (atomEnv ρ) in
  lem-sub-zero u v k (complete v u auto ⟨≡⟩ auto)
⟨-⟩-sound a b ρ | []     , d ∷ ds | complete =
  let u = ⟦ a      ⟧n (atomEnv ρ)
      v = ⟦ b      ⟧n (atomEnv ρ)
      k = ⟦ d ∷ ds ⟧n (atomEnv ρ) in
  lem-zero-sub u v k (auto ⟨≡⟩ complete v u auto)
⟨-⟩-sound a b ρ | u ∷ us , v ∷ vs | complete =
  let eval = λ x → ⟦ x ⟧n (atomEnv ρ) in
  auto ⟨≡⟩ cong₂ _-_ (lem-sub-eval (u ∷ us) ρ) (lem-sub-eval (v ∷ vs) ρ) ⟨≡⟩
  lem-sub (eval a) (eval b) (eval (u ∷ us)) (eval (v ∷ vs)) (complete (eval b) (eval a) auto)

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
  ⟨*⟩-sound (normSub e) (normSub e₁) (atomEnv ρ) ʳ⟨≡⟩ʳ
  lem-sub-eval (normSub (e ⟨*⟩ e₁)) ρ
sound-sub (e ⟨-⟩ e₁) ρ =
  cong₂ _-_ (sound-sub e  ρ ⟨≡⟩ lem-sub-eval (normSub e)  ρ)
            (sound-sub e₁ ρ ⟨≡⟩ lem-sub-eval (normSub e₁) ρ) ⟨≡⟩
  ⟨-⟩-sound (normSub e) (normSub e₁) ρ ʳ⟨≡⟩ʳ
  lem-sub-eval (normSub (e ⟨-⟩ e₁)) ρ
