
module Prelude.Product where

open import Agda.Primitive
open import Prelude.Function
open import Prelude.Equality
open import Prelude.Decidable
open import Prelude.Ord

infixr 1 _,_
data Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  _,_ : (x : A) (y : B x) → Σ A B

instance
  ipair : ∀ {a b} {A : Set a} {B : A → Set b} {{x : A}} {{y : B x}} → Σ A B
  ipair {{x}} {{y}} = x , y

fst : ∀ {a b} {A : Set a} {B : A → Set b} → Σ A B → A
fst (x , y) = x

snd : ∀ {a b} {A : Set a} {B : A → Set b} (p : Σ A B) → B (fst p)
snd (x , y) = y

infixr 3 _×_
_×_ : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
A × B = Σ A (λ _ → B)

_,′_ : ∀ {a b} {A : Set a} {B : Set b} → A → B → A × B
_,′_ = _,_

uncurry : ∀ {a b c} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c} →
            (∀ x (y : B x) → C x y) → (p : Σ A B) → C (fst p) (snd p)
uncurry f (x , y) = f x y

uncurry′ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Set c} →
            (∀ x → B x → C) → Σ A B → C
uncurry′ f (x , y) = f x y

curry : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Σ A B → Set c} →
          (∀ p → C p) → ∀ x (y : B x) → C (x , y)
curry f x y = f (x , y)

infixr 3 _***_ _***′_ _&&&_
_***_ : ∀ {a₁ a₂ b₁ b₂} {A₁ : Set a₁} {A₂ : Set a₂} {B₁ : A₁ → Set b₁} {B₂ : A₂ → Set b₂}
          (f : A₁ → A₂) → (∀ {x} → B₁ x → B₂ (f x)) → Σ A₁ B₁ → Σ A₂ B₂
(f *** g) (x , y) = f x , g y

_***′_ : ∀ {a₁ a₂ b₁ b₂} {A₁ : Set a₁} {A₂ : Set a₂} {B₁ : Set b₁} {B₂ : Set b₂} →
          (A₁ → A₂) → (B₁ → B₂) → A₁ × B₁ → A₂ × B₂
(f ***′ g) (x , y) = f x , g y

_&&&_ : ∀ {c a b} {C : Set c} {A : Set a} {B : A → Set b}
          (f : C → A) → (∀ x → B (f x)) → C → Σ A B
(f &&& g) x = f x , g x

first : ∀ {a₁ a₂ b} {A₁ : Set a₁} {A₂ : Set a₂} {B : Set b} →
          (A₁ → A₂) → A₁ × B → A₂ × B
first f = f *** id

second : ∀ {a b₁ b₂} {A : Set a} {B₁ : A → Set b₁} {B₂ : A → Set b₂} →
           (∀ {x} → B₁ x → B₂ x) → Σ A B₁ → Σ A B₂
second f = id *** f

-- Eq instance --

sigma-inj-fst : ∀ {a b} {A : Set a} {B : A → Set b} {x : A} {y : B x}
                 {x₁ : A} {y₁ : B x₁} →
               (x , y) ≡ (x₁ , y₁) → x ≡ x₁
sigma-inj-fst refl = refl

sigma-inj-snd : ∀ {a b} {A : Set a} {B : A → Set b} {x : A} {y y₁ : B x} →
               _≡_ {A = Σ A B} (x , y) (x , y₁) → y ≡ y₁
sigma-inj-snd refl = refl

instance
  EqSigma : ∀ {a b} {A : Set a} {B : A → Set b} {{EqA : Eq A}} {{EqB : ∀ {x} → Eq (B x)}} → Eq (Σ A B)
  EqSigma {A = A} {B} = record { _==_ = eqSigma }
    where
      eqSigma : (x y : Σ A B) → Dec (x ≡ y)
      eqSigma (x , y) (x₁ , y₁) with x == x₁
      eqSigma (x , y) (x₁ , y₁) | no  neq  = no λ eq → neq (sigma-inj-fst eq)
      eqSigma (x , y) (.x , y₁) | yes refl with y == y₁
      eqSigma (x , y) (.x , y₁) | yes refl | no neq = no λ eq → neq (sigma-inj-snd eq)
      eqSigma (x , y) (.x , .y) | yes refl | yes refl = yes refl

-- Ord instance --

data LexiographicOrder {a b} {A : Set a} {B : A → Set b}
                       (_<A_ : A → A → Set a) (_<B_ : ∀ {x} → B x → B x → Set b) :
                       Σ A B → Σ A B → Set (a ⊔ b) where
  fst< : ∀ {x₁ x₂} {y₁ : B x₁} {y₂ : B x₂} → x₁ <A x₂ → LexiographicOrder _<A_ _<B_ (x₁ , y₁) (x₂ , y₂)
  snd< : ∀ {x} {y₁ y₂ : B x} → y₁ <B y₂ → LexiographicOrder _<A_ _<B_ (x , y₁) (x , y₂)

module _ {a b} {A : Set a} {B : A → Set b} {{OrdA : Ord A}} {{OrdB : ∀ {x} → Ord (B x)}} where
  private
    cmpSigma : (x y : Σ A B) → Comparison (LexiographicOrder _<_ _<_) x y
    cmpSigma (x , y)  (x₁ , y₁)  with compare x x₁
    cmpSigma (x , y)  (x₁ , y₁)  | less x<x₁    = less    (fst< x<x₁)
    cmpSigma (x , y)  (x₁ , y₁)  | greater x₁<x = greater (fst< x₁<x)
    cmpSigma (x , y)  (.x , y₁)  | equal refl with compare y y₁
    cmpSigma (x₁ , y) (.x₁ , y₁) | equal refl | less y<y₁    = less    (snd< y<y₁)
    cmpSigma (x₁ , y) (.x₁ , y₁) | equal refl | greater y₁<y = greater (snd< y₁<y)
    cmpSigma (x₁ , y) (.x₁ , .y) | equal refl | equal refl   = equal refl

    from-eq : (x y : Σ A B) → x ≡ y → LexiographicOrder _<_ _≤_ x y
    from-eq (x , y) (.x , .y) refl = snd< (eq-to-leq (refl {x = y}))

    from-lt : (x y : Σ A B) → LexiographicOrder _<_ _<_ x y → LexiographicOrder _<_ _≤_ x y
    from-lt (x₁ , y₁) (x₂ , y₂) (fst< lt) = fst< lt
    from-lt (x  , y₁) (.x , y₂) (snd< lt) = snd< (lt-to-leq {x = y₁} lt)

    from-leq : (x y : Σ A B) → LexiographicOrder _<_ _≤_ x y → LessEq (LexiographicOrder _<_ _<_) x y
    from-leq (a , b) (a₁ , b₁) (fst< a<a₁) = less (fst< a<a₁)
    from-leq (a , b) (.a , b₁) (snd< b≤b₁) with leq-to-lteq {{OrdB}} b≤b₁
    ... | less b<b₁  = less (snd< b<b₁)
    ... | equal b=b₁ = equal ((a ,_) $≡ b=b₁)

  instance
    OrdSigma : Ord (Σ A B)
    Ord._<_         OrdSigma = _
    Ord._≤_         OrdSigma = LexiographicOrder _<_ _≤_
    Ord.compare     OrdSigma = cmpSigma
    Ord.eq-to-leq   OrdSigma = from-eq _ _
    Ord.lt-to-leq   OrdSigma = from-lt _ _
    Ord.leq-to-lteq OrdSigma = from-leq _ _
