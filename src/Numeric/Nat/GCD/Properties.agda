
module Numeric.Nat.GCD.Properties where

open import Prelude
open import Numeric.Nat.Divide
open import Numeric.Nat.Divide.Properties
open import Numeric.Nat.GCD
open import Numeric.Nat.GCD.Extended
open import Tactic.Nat
open import Tactic.Cong

--- Properties ---

gcd-divides-l : ∀ a b → gcd! a b Divides a
gcd-divides-l a b with gcd a b
... | gcd-res _ i = IsGCD.d|a i

gcd-divides-r : ∀ a b → gcd! a b Divides b
gcd-divides-r a b with gcd a b
... | gcd-res _ i = IsGCD.d|b i

is-gcd-unique : ∀ {a b} d₁ d₂ (g₁ : IsGCD d₁ a b) (g₂ : IsGCD d₂ a b) → d₁ ≡ d₂
is-gcd-unique d d′ (is-gcd d|a d|b gd) (is-gcd d′|a d′|b gd′) =
  divides-antisym (gd′ d d|a d|b)
                  (gd  d′ d′|a d′|b)

gcd-unique : ∀ a b d → IsGCD d a b → gcd! a b ≡ d
gcd-unique a b d pd with gcd a b
... | gcd-res d′ pd′ = is-gcd-unique d′ d pd′ pd

is-gcd-commute : ∀ {d a b} → IsGCD d a b → IsGCD d b a
is-gcd-commute (is-gcd d|a d|b g) = is-gcd d|b d|a (flip ∘ g)

gcd-commute : ∀ a b → gcd! a b ≡ gcd! b a
gcd-commute a b with gcd b a
gcd-commute a b | gcd-res d p = gcd-unique a b d (is-gcd-commute p)

gcd-factor-l : ∀ {a b} → a Divides b → gcd! a b ≡ a
gcd-factor-l {a} (factor! b) =
  gcd-unique a (b * a) a
             (is-gcd divides-refl (divides-mul-r b divides-refl) λ _ k|a _ → k|a)

gcd-factor-r : ∀ {a b} → b Divides a → gcd! a b ≡ b
gcd-factor-r {a} {b} b|a = gcd-commute a b ⟨≡⟩ gcd-factor-l b|a

gcd-idem : ∀ a → gcd! a a ≡ a
gcd-idem a = gcd-factor-l divides-refl

gcd-zero-l : ∀ n → gcd! 0 n ≡ n
gcd-zero-l n = gcd-unique 0 n n (is-gcd (factor! 0) divides-refl λ _ _ k|n → k|n)

gcd-zero-r : ∀ n → gcd! n 0 ≡ n
gcd-zero-r n = gcd-commute n 0 ⟨≡⟩ gcd-zero-l n

zero-is-gcd-l : ∀ {a b} → IsGCD 0 a b → a ≡ 0
zero-is-gcd-l (is-gcd 0|a _ _) = divides-zero 0|a

zero-is-gcd-r : ∀ {a b} → IsGCD 0 a b → b ≡ 0
zero-is-gcd-r (is-gcd _ 0|b _) = divides-zero 0|b

zero-gcd-l : ∀ a b → gcd! a b ≡ 0 → a ≡ 0
zero-gcd-l a b eq with gcd a b
zero-gcd-l a b refl | gcd-res .0 p = zero-is-gcd-l p

zero-gcd-r : ∀ a b → gcd! a b ≡ 0 → b ≡ 0
zero-gcd-r a b eq with gcd a b
zero-gcd-r a b refl | gcd-res .0 p = zero-is-gcd-r p

nonzero-is-gcd-l : ∀ {a b d} {{_ : NonZero a}} → IsGCD d a b → NonZero d
nonzero-is-gcd-l {0} {{}} _
nonzero-is-gcd-l {a@(suc _)} {d = suc _} _ = _
nonzero-is-gcd-l {a@(suc _)} {d = 0} (is-gcd (factor q eq) _ _) = refute eq

nonzero-is-gcd-r : ∀ {a b d} {{_ : NonZero b}} → IsGCD d a b → NonZero d
nonzero-is-gcd-r isgcd = nonzero-is-gcd-l (is-gcd-commute isgcd)

nonzero-gcd-l : ∀ a b {{_ : NonZero a}} → NonZero (gcd! a b)
nonzero-gcd-l a b = nonzero-is-gcd-l (GCD.isGCD (gcd a b))

nonzero-gcd-r : ∀ a b {{_ : NonZero b}} → NonZero (gcd! a b)
nonzero-gcd-r a b = nonzero-is-gcd-r (GCD.isGCD (gcd a b))

private
  _|>_ = divides-trans

gcd-assoc : ∀ a b c → gcd! a (gcd! b c) ≡ gcd! (gcd! a b) c
gcd-assoc a b c with gcd a b | gcd b c
... | gcd-res ab (is-gcd ab|a ab|b gab)
    | gcd-res bc (is-gcd bc|b bc|c gbc) with gcd ab c
...    | gcd-res ab-c (is-gcd abc|ab abc|c gabc) =
  gcd-unique a bc ab-c
             (is-gcd (abc|ab |> ab|a)
                     (gbc ab-c (abc|ab |> ab|b) abc|c)
                     λ k k|a k|bc → gabc k (gab k k|a (k|bc |> bc|b))
                                           (k|bc |> bc|c))

coprime-sym : ∀ a b → Coprime a b → Coprime b a
coprime-sym a b p = gcd-commute b a ⟨≡⟩ p

coprimeByDivide : ∀ a b → (∀ k → k Divides a → k Divides b → k Divides 1) → Coprime a b
coprimeByDivide a b g = gcd-unique a b 1 (is-gcd one-divides one-divides g)

divide-coprime : ∀ d a b → Coprime a b → d Divides a → d Divides b → d Divides 1
divide-coprime d a b p d|a d|b with gcd a b
divide-coprime d a b refl d|a d|b | gcd-res _ (is-gcd _ _ g) =
  g d d|a d|b

mul-coprime-l : ∀ a b c → Coprime a (b * c) → Coprime a b
mul-coprime-l a b c a⊥bc =
  coprimeByDivide a b λ k k|a k|b →
    divide-coprime k a (b * c) a⊥bc k|a (divides-mul-l c k|b)

mul-coprime-r : ∀ a b c → Coprime a (b * c) → Coprime a c
mul-coprime-r a b c a⊥bc = mul-coprime-l a c b (transport (Coprime a) auto a⊥bc)

is-gcd-factors-coprime : ∀ {a b d} (p : IsGCD d a b) {{_ : NonZero d}} →
                           Coprime (is-gcd-factor₁ p) (is-gcd-factor₂ p)
is-gcd-factors-coprime {a} {b} {0} _ {{}}
is-gcd-factors-coprime {a} {b} {d@(suc _)} p@(is-gcd (factor qa refl) (factor qb refl) g) with gcd qa qb
... | gcd-res j (is-gcd j|qa j|qb gj) = lem₃ j lem₂
  where
    lem : IsGCD (j * d) a b
    lem = is-gcd (divides-mul-cong-r d j|qa) (divides-mul-cong-r d j|qb) λ k k|a k|b →
                 divides-mul-r j (g k k|a k|b)

    lem₂ : d ≡ j * d
    lem₂ = is-gcd-unique d (j * d) p lem

    lem₃ : ∀ j → d ≡ j * d → j ≡ 1
    lem₃ 0 ()
    lem₃ 1 _ = refl
    lem₃ (suc (suc n)) eq = refute eq

-- Divide two numbers by their gcd and return the result, the gcd, and some useful properties.
-- Continuation-passing for efficiency reasons.
gcdReduce : ∀ {a} {A : Set a} (a b : Nat) ⦃ _ : NonZero b ⦄ →
           ((a′ b′ d : Nat) → (⦃ _ : NonZero a ⦄ → NonZero a′) →
                              ⦃ nzb : NonZero b′ ⦄ → ⦃ nzd : NonZero d ⦄ →
                               a′ * d ≡ a → b′ * d ≡ b →
                               Coprime a′ b′ → A) → A
gcdReduce a b ret with gcd a b
gcdReduce a b ret | gcd-res d isgcd@(is-gcd d|a@(factor a′ eqa) d|b@(factor b′ eqb) g)=
  let instance _ = nonzero-is-gcd-r isgcd in
  ret a′ b′ d (nonzero-factor d|a) ⦃ nonzero-factor d|b ⦄
              eqa eqb
              (is-gcd-factors-coprime isgcd)

--- Properties ---

coprime-divide-mul-l : ∀ a b c → Coprime a b → a Divides (b * c) → a Divides c
coprime-divide-mul-l a b c p a|bc with extendedGCD a b
coprime-divide-mul-l a b c p a|bc | gcd-res d i e with gcd-unique _ _ _ i ʳ⟨≡⟩ p
coprime-divide-mul-l a b c p (factor q qa=bc) | gcd-res d i (bézoutL x y ax=1+by) | refl =
  factor (x * c - y * q) $
    (x * c - y * q) * a
      ≡⟨ auto ⟩
    a * x * c - y * (q * a)
      ≡⟨ by-cong ax=1+by ⟩
    suc (b * y) * c - y * (q * a)
      ≡⟨ by-cong qa=bc ⟩
    suc (b * y) * c - y * (b * c)
      ≡⟨ auto ⟩
    c ∎
coprime-divide-mul-l a b c p (factor q qa=bc) | gcd-res d i (bézoutR x y by=1+ax) | refl =
  factor (y * q - x * c) $
    (y * q - x * c) * a
      ≡⟨ auto ⟩
    y * (q * a) - a * x * c
      ≡⟨ by-cong qa=bc ⟩
    y * (b * c) - a * x * c
      ≡⟨ auto ⟩
    (b * y) * c - a * x * c
      ≡⟨ by-cong by=1+ax ⟩
    suc (a * x) * c - a * x * c
      ≡⟨ auto ⟩
    c ∎

coprime-divide-mul-r : ∀ a b c → Coprime a c → a Divides (b * c) → a Divides b
coprime-divide-mul-r a b c p a|bc =
  coprime-divide-mul-l a c b p (transport (a Divides_) auto a|bc)

is-gcd-by-coprime-factors : ∀ d a b (d|a : d Divides a) (d|b : d Divides b) ⦃ nzd : NonZero d ⦄ →
                            Coprime (get-factor d|a) (get-factor d|b) →
                            IsGCD d a b
is-gcd-by-coprime-factors d a b d|a@(factor! q) d|b@(factor! r) q⊥r =
  is-gcd d|a d|b λ k k|a k|b →
    let lem : ∀ j → j Divides q → j Divides r → j ≡ 1
        lem j j|q j|r = divides-one (divide-coprime j q r q⊥r j|q j|r)
    in
    case gcd k d of λ where
      (gcd-res g isgcd@(is-gcd (factor k′ k′g=k@refl) (factor d′ d′g=d@refl) sup)) →
        let instance g>0 = nonzero-is-gcd-r isgcd
            k′⊥d′ : Coprime k′ d′
            k′⊥d′ = is-gcd-factors-coprime isgcd
            k′|qd′ : k′ Divides (q * d′)
            k′|qd′ = cancel-mul-divides-r k′ (q * d′) g
                       (transport ((k′ * g) Divides_) {x = q * (d′ * g)} {q * d′ * g} auto k|a)
            k′|rd′ : k′ Divides (r * d′)
            k′|rd′ = cancel-mul-divides-r k′ (r * d′) g
                       (transport ((k′ * g) Divides_) {x = r * (d′ * g)} {r * d′ * g} auto k|b)
            k′|q : k′ Divides q
            k′|q = coprime-divide-mul-r k′ q d′ k′⊥d′ k′|qd′
            k′|r : k′ Divides r
            k′|r = coprime-divide-mul-r k′ r d′ k′⊥d′ k′|rd′
            k′=1 = lem k′ k′|q k′|r
            k=g : k ≡ g
            k=g = case k′=1 of λ where refl → auto
        in factor d′ (d′ *_ $≡ k=g ⟨≡⟩ d′g=d)
