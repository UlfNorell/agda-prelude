module Tactic.Nat.Subtract.Lemmas where

open import Prelude
open import Tactic.Nat.NF
open import Tactic.Nat.Exp
open import Container.Bag
open import Tactic.Nat.Simpl
open import Prelude.Nat.Properties
open import Prelude.List.Properties
open import Tactic.Nat.Auto.Lemmas
open import Tactic.Nat.Simpl.Lemmas
open import Tactic.Nat.Auto
open import Tactic.Nat.Simpl

open import Tactic.Nat.Subtract.Exp

sub-cancel : (a : Nat) → a - a ≡ 0
sub-cancel zero = refl
sub-cancel (suc a) = sub-cancel a

sub-add-r : (a b c : Nat) → a - (b + c) ≡ a - b - c
sub-add-r  a       zero    c      = refl
sub-add-r zero    (suc b)  zero   = refl
sub-add-r zero    (suc b) (suc c) = refl
sub-add-r (suc a) (suc b)  c      = sub-add-r a b c

lem-sub-zero : (a b c : Nat) → b + c ≡ a → c ≡ a - b
lem-sub-zero ._  zero   c refl = refl
lem-sub-zero ._ (suc b) c refl = lem-sub-zero _ b c refl

lem-zero-sub : (a b c : Nat) → b ≡ a + c → 0 ≡ a - b
lem-zero-sub  zero   ._  zero   refl = refl
lem-zero-sub  zero   ._ (suc c) refl = refl
lem-zero-sub (suc a) ._  c      refl = lem-zero-sub a _ c refl

lem-sub : (a b u v : Nat) → b + u ≡ a + v → u - v ≡ a - b
lem-sub  zero    zero   u ._ refl = sub-cancel u
lem-sub  zero   (suc b) u ._ refl = sym $ lem-zero-sub u (suc b + u) (suc b) auto
lem-sub (suc a)  zero  ._  v refl = sym $ lem-sub-zero (suc a + v) v (suc a) auto
lem-sub (suc a) (suc b) u  v eq   = lem-sub a b u v (suc-inj eq)

sub-mul-distr-l : (a b c : Nat) → (a - b) * c ≡ a * c - b * c
sub-mul-distr-l zero b c = (_* c) $≡ lem-zero-sub 0 b b refl ʳ⟨≡⟩ lem-zero-sub 0 (b * c) (b * c) refl
sub-mul-distr-l (suc a) zero c = refl
sub-mul-distr-l (suc a) (suc b) c =
  sub-mul-distr-l a b c ⟨≡⟩
  lem-sub (suc a * c) (suc b * c) (a * c) (b * c) auto

sub-mul-distr-r : (a b c : Nat) → a * (b - c) ≡ a * b - a * c
sub-mul-distr-r a b c =
  auto ⟨≡⟩ sub-mul-distr-l b c a
       ⟨≡⟩ cong₂ _-_ (mul-commute b a) (mul-commute c a)

-- The evaluator that doesn't generate x * 1 + 0 is the same as the
-- one that does.

lem-eval-sns-sn : ∀ n ρ → ⟦ n ⟧sns ρ ≡ ⟦ n ⟧sn ρ

private
  lem-eval-sns-sn-t : ∀ t ρ → ⟦ t ⟧sts ρ ≡ ⟦ t ⟧st ρ
  lem-eval-sns-sn-a : ∀ a ρ → ⟦ a ⟧sas ρ ≡ ⟦ a ⟧sa ρ

  lem-eval-sns-sn-a (var x) ρ = refl
  lem-eval-sns-sn-a (a ⟨-⟩ b) ρ = _-_ $≡ lem-eval-sns-sn a ρ *≡ lem-eval-sns-sn b ρ

  lem-eval-sns-sn-t []          ρ = refl
  lem-eval-sns-sn-t (x ∷ [])    ρ = lem-eval-sns-sn-a x ρ ⟨≡⟩ auto
  lem-eval-sns-sn-t (x ∷ y ∷ t) ρ = _*_ $≡ lem-eval-sns-sn-a x ρ *≡ lem-eval-sns-sn-t (y ∷ t) ρ

lem-eval-sns-sn []                 ρ = refl
lem-eval-sns-sn ((k , t) ∷ [])     ρ = _*_ k $≡ lem-eval-sns-sn-t t ρ ⟨≡⟩ auto
lem-eval-sns-sn ((k , t) ∷ t₁ ∷ n) ρ = _+_ $≡ (_*_ k $≡ lem-eval-sns-sn-t t ρ)
                                         *≡ lem-eval-sns-sn (t₁ ∷ n) ρ

-- The evaluation that the termination checker lets us write is the
-- same as the one we want to write.

private
  lem-eval-sn-n-t : ∀ t ρ → ⟦ t ⟧st ρ ≡ productR (map (atomEnv ρ) t)
  lem-eval-sn-n-t [] ρ = refl
  lem-eval-sn-n-t (x ∷ t) ρ = (⟦ x ⟧sa ρ *_) $≡ lem-eval-sn-n-t t ρ

lem-eval-sn-n   : ∀ n ρ → ⟦ n ⟧sn ρ ≡ ⟦ n ⟧n (atomEnv ρ)
lem-eval-sn-n []            ρ = refl
lem-eval-sn-n ((k , t) ∷ n) ρ = _+_ $≡ (_*_ k $≡ lem-eval-sn-n-t t ρ) *≡ lem-eval-sn-n n ρ

private
  lem-env : ∀ ρ x → atomEnvS ρ x ≡ atomEnv ρ x
  lem-env ρ (var x) = refl
  lem-env ρ (a ⟨-⟩ b) = _-_ $≡ lem-eval-sns-sn a ρ *≡ lem-eval-sns-sn b ρ

-- Combining the above equalities.

lem-eval-sn-nS : ∀ n ρ → ⟦ n ⟧sn ρ ≡ ⟦ n ⟧n (atomEnvS ρ)
lem-eval-sn-nS n ρ = lem-eval-sn-n n ρ ⟨≡⟩ʳ lem-eval-env (atomEnvS ρ) (atomEnv ρ) (lem-env ρ) n

lem-eval-sns-nS : ∀ n ρ → ⟦ n ⟧sns ρ ≡ ⟦ n ⟧n (atomEnvS ρ)
lem-eval-sns-nS n ρ = lem-eval-sns-sn n ρ ⟨≡⟩ lem-eval-sn-nS n ρ

lem-eval-sns-ns : ∀ n ρ → ⟦ n ⟧sns ρ ≡ ⟦ n ⟧ns (atomEnvS ρ)
lem-eval-sns-ns n ρ = lem-eval-sns-nS n ρ ⟨≡⟩ʳ ns-sound n (atomEnvS ρ)

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
  (⟦ u ∷ us ⟧sn ρ - ⟦ v ∷ vs ⟧sn ρ) * 1 + 0 + 0
    ≡⟨ auto ⟩
  ⟦ u ∷ us ⟧sn ρ - ⟦ v ∷ vs ⟧sn ρ
    ≡⟨ cong₂ _-_ (lem-eval-sn-n (u ∷ us) ρ) (lem-eval-sn-n (v ∷ vs) ρ) ⟩
  eval (u ∷ us) - eval (v ∷ vs)
    ≡⟨ lem-sub (eval a) (eval b) (eval (u ∷ us)) (eval (v ∷ vs)) (complete (eval b) (eval a) auto) ⟩
  eval a - eval b ∎

⟨-⟩-sound : ∀ a b ρ → ⟦ a -nf b ⟧n (atomEnv ρ) ≡ ⟦ a ⟧n (atomEnv ρ) - ⟦ b ⟧n (atomEnv ρ)
⟨-⟩-sound a b ρ with is-subtraction a
⟨-⟩-sound a b ρ  | no     = ⟨-⟩-sound′ a b ρ
⟨-⟩-sound ._ c ρ | a ⟨-⟩ b =
  let eval = λ x → ⟦ x ⟧n (atomEnv ρ) in
  ⟨-⟩-sound′ a (b +nf c) ρ ⟨≡⟩
  (eval a -_) $≡ ⟨+⟩-sound b c (atomEnv ρ) ⟨≡⟩
  sub-add-r (eval a) (eval b) (eval c) ⟨≡⟩
  (_- eval c) $≡ (_-_ $≡ lem-eval-sn-n a ρ *≡ lem-eval-sn-n b ρ) ʳ⟨≡⟩
  (_- eval c) $≡ auto

⟨*⟩-sound₁ : ∀ a b ρ → ⟦ a *nf₁ b ⟧n (atomEnv ρ) ≡ ⟦ a ⟧n (atomEnv ρ) * ⟦ b ⟧n (atomEnv ρ)

private
  sound-mul-ktm′ : ∀ t a ρ → ⟦ t *ktm′ a ⟧n (atomEnv ρ) ≡ ⟦ t ⟧t (atomEnv ρ) * ⟦ a ⟧n (atomEnv ρ)

  sound-mul-tm : ∀ s t ρ → ⟦ s *tm t ⟧n (atomEnv ρ) ≡ ⟦ s ⟧t (atomEnv ρ) * ⟦ t ⟧t (atomEnv ρ)
  sound-mul-tm s t ρ with is-subtraction-tm t
  sound-mul-tm (x , a) (y , b) ρ | no =
    follows-from (x * y *_ $≡ map-merge a b (atomEnv ρ))
  sound-mul-tm s ._ ρ | a ⟨-⟩ b =
    let eval  x = ⟦ x ⟧n (atomEnv ρ)
        evalt x = ⟦ x ⟧t (atomEnv ρ) in
    ⟨-⟩-sound (s *ktm′ a) (s *ktm′ b) ρ ⟨≡⟩
    _-_ $≡ sound-mul-ktm′ s a ρ *≡ sound-mul-ktm′ s b ρ ⟨≡⟩
    sub-mul-distr-r (evalt s) (eval a) (eval b) ʳ⟨≡⟩
    (evalt s *_) $≡ (_-_ $≡ lem-eval-sn-n a ρ *≡ lem-eval-sn-n b ρ) ʳ⟨≡⟩
    auto

  sound-mul-ktm′ t [] ρ = auto
  sound-mul-ktm′ t (x ∷ a) ρ =
    let eval  x = ⟦ x ⟧n (atomEnv ρ)
        evalt x = ⟦ x ⟧t (atomEnv ρ) in
    ⟨+⟩-sound (t *tm x) (t *ktm′ a) (atomEnv ρ) ⟨≡⟩
    _+_ $≡ sound-mul-tm t x ρ *≡ sound-mul-ktm′ t a ρ ⟨≡⟩ʳ
    mul-distr-l (evalt t) (evalt x) (eval a)

  sound-mul-ktm : ∀ t a ρ → ⟦ t *ktm a ⟧n (atomEnv ρ) ≡ ⟦ t ⟧t (atomEnv ρ) * ⟦ a ⟧n (atomEnv ρ)
  sound-mul-ktm t a ρ with is-subtraction-tm t
  sound-mul-ktm t  a ρ | no = sound-mul-ktm′ t a ρ
  sound-mul-ktm ._ c ρ | a ⟨-⟩ b =
    let eval x = ⟦ x ⟧n (atomEnv ρ) in
    ⟨-⟩-sound (a *nf₁ c) (b *nf₁ c) ρ ⟨≡⟩
    _-_ $≡ ⟨*⟩-sound₁ a c ρ *≡ ⟨*⟩-sound₁ b c ρ ⟨≡⟩
    sub-mul-distr-l (eval a) (eval b) (eval c) ʳ⟨≡⟩
    (_* eval c) $≡ (_-_ $≡ lem-eval-sn-n a ρ *≡ lem-eval-sn-n b ρ) ʳ⟨≡⟩
    auto

⟨*⟩-sound₁ [] b ρ = refl
⟨*⟩-sound₁ (t ∷ a) b ρ =
  let eval x = ⟦ x ⟧n (atomEnv ρ)
      evalt x = ⟦ x ⟧t (atomEnv ρ) in
  ⟨+⟩-sound (t *ktm b) (a *nf₁ b) (atomEnv ρ) ⟨≡⟩
  _+_ $≡ sound-mul-ktm t b ρ *≡ ⟨*⟩-sound₁ a b ρ ⟨≡⟩ʳ
  mul-distr-r (evalt t) (eval a) (eval b)

sound-sub : ∀ e ρ → ⟦ e ⟧se ρ ≡ ⟦ normSub e ⟧sn ρ
sound-sub (var x) ρ = auto
sound-sub (lit 0) ρ = refl
sound-sub (lit (suc n)) ρ = auto
sound-sub (e ⟨+⟩ e₁) ρ =
  cong₂ _+_ (sound-sub e  ρ ⟨≡⟩ lem-eval-sn-n (normSub e)  ρ)
            (sound-sub e₁ ρ ⟨≡⟩ lem-eval-sn-n (normSub e₁) ρ) ⟨≡⟩
  ⟨+⟩-sound (normSub e) (normSub e₁) (atomEnv ρ) ʳ⟨≡⟩ʳ
  lem-eval-sn-n (normSub (e ⟨+⟩ e₁)) ρ
sound-sub (e ⟨*⟩ e₁) ρ =
  cong₂ _*_ (sound-sub e  ρ ⟨≡⟩ lem-eval-sn-n (normSub e)  ρ)
            (sound-sub e₁ ρ ⟨≡⟩ lem-eval-sn-n (normSub e₁) ρ) ⟨≡⟩
  ⟨*⟩-sound₁ (normSub e) (normSub e₁) ρ ʳ⟨≡⟩ʳ
  lem-eval-sn-n (normSub (e ⟨*⟩ e₁)) ρ
sound-sub (e ⟨-⟩ e₁) ρ =
  cong₂ _-_ (sound-sub e  ρ ⟨≡⟩ lem-eval-sn-n (normSub e)  ρ)
            (sound-sub e₁ ρ ⟨≡⟩ lem-eval-sn-n (normSub e₁) ρ) ⟨≡⟩
  ⟨-⟩-sound (normSub e) (normSub e₁) ρ ʳ⟨≡⟩ʳ
  lem-eval-sn-n (normSub (e ⟨-⟩ e₁)) ρ

liftNFSubEq : ∀ e₁ e₂ ρ → ⟦ normSub e₁ ⟧sn ρ ≡ ⟦ normSub e₂ ⟧sn ρ → ⟦ e₁ ⟧se ρ ≡ ⟦ e₂ ⟧se ρ
liftNFSubEq e₁ e₂ ρ eq = eraseEquality $ sound-sub e₁ ρ ⟨≡⟩ eq ⟨≡⟩ʳ sound-sub e₂ ρ

unliftNFSubEq : ∀ e₁ e₂ ρ → ⟦ e₁ ⟧se ρ ≡ ⟦ e₂ ⟧se ρ → ⟦ normSub e₁ ⟧sn ρ ≡ ⟦ normSub e₂ ⟧sn ρ
unliftNFSubEq e₁ e₂ ρ eq = eraseEquality $ sound-sub e₁ ρ ʳ⟨≡⟩ eq ⟨≡⟩ sound-sub e₂ ρ

SubExpEq : SubExp → SubExp → Env Var → Set
SubExpEq e₁ e₂ ρ = ⟦ e₁ ⟧se ρ ≡ ⟦ e₂ ⟧se ρ

CancelSubEq : SubExp → SubExp → Env Var → Set
CancelSubEq e₁ e₂ ρ = NFEqS (cancel (normSub e₁) (normSub e₂)) (atomEnvS ρ)

simplifySubEq : ∀ e₁ e₂ (ρ : Env Var) → CancelSubEq e₁ e₂ ρ → SubExpEq e₁ e₂ ρ
simplifySubEq e₁ e₂ ρ H = liftNFSubEq e₁ e₂ ρ $
  lem-eval-sn-nS (normSub e₁) ρ ⟨≡⟩
  cancel-sound (normSub e₁) (normSub e₂) (atomEnvS ρ) H ⟨≡⟩ʳ
  lem-eval-sn-nS (normSub e₂) ρ

complicateSubEq : ∀ e₁ e₂ ρ → SubExpEq e₁ e₂ ρ → CancelSubEq e₁ e₂ ρ
complicateSubEq e₁ e₂ ρ H =
  cancel-complete (normSub e₁) (normSub e₂) (atomEnvS ρ) $
  lem-eval-sn-nS (normSub e₁) ρ ʳ⟨≡⟩
  unliftNFSubEq e₁ e₂ ρ H ⟨≡⟩
  lem-eval-sn-nS (normSub e₂) ρ
