
module Prelude.Product where

open import Agda.Primitive
open import Prelude.Function
open import Prelude.Equality
open import Prelude.Decidable
open import Prelude.Ord

infixr 1 _,_
data Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
 _,_ : (x : A) (y : B x) → Σ A B

fst : ∀ {a b} {A : Set a} {B : A → Set b} → Σ A B → A
fst (x , y) = x

snd : ∀ {a b} {A : Set a} {B : A → Set b} (p : Σ A B) → B (fst p)
snd (x , y) = y

infixr 3 _×_
_×_ : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
A × B = Σ A (λ _ → B)

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

pair-inj-fst : ∀ {a b} {A : Set a} {B : Set b} {x : A} {y : B}
                 {x₁ : A} {y₁ : B} →
               (x , y) ≡ (x₁ , y₁) → x ≡ x₁
pair-inj-fst refl = refl

pair-inj-snd : ∀ {a b} {A : Set a} {B : Set b} {x : A} {y : B}
                 {x₁ : A} {y₁ : B} →
               (x , y) ≡ (x₁ , y₁) → y ≡ y₁
pair-inj-snd refl = refl

private
  eqPair : ∀ {a b} {A : Set a} {B : Set b} {{EqA : Eq A}} {{EqB : Eq B}}
             (x y : A × B) → Dec (x ≡ y)
  eqPair (x , y) (x₁ , y₁) with x == x₁ | y == y₁
  eqPair (x , y) (.x , .y) | yes refl | yes refl = yes refl
  eqPair (x , y) (x₁ , y₁) | _        | no neq  = no λ eq → neq (pair-inj-snd eq)
  eqPair (x , y) (x₁ , y₁) | no neq   | _       = no λ eq → neq (pair-inj-fst eq)

EqPair : ∀ {a b} {A : Set a} {B : Set b} {{EqA : Eq A}} {{EqB : Eq B}} → Eq (A × B)
EqPair = record { _==_ = eqPair }

-- Ord instance --

data LessPair {a b} {A : Set a} {B : Set b} {{OrdA : Ord A}} {{OrdB : Ord B}} :
              A × B → A × B → Set (a ⊔ b) where
  fst< : ∀ {x₁ x₂ y₁ y₂} → LessThan x₁ x₂ → LessPair (x₁ , y₁) (x₂ , y₂)
  snd< : ∀ {x y₁ y₂} → LessThan y₁ y₂ → LessPair (x , y₁) (x , y₂)

private
  cmpPair : ∀ {a b} {A : Set a} {B : Set b} {{OrdA : Ord A}} {{OrdB : Ord B}} →
            (x y : A × B) → Comparison LessPair x y
  cmpPair (x , y) (x₁ , y₁) with compare x x₁
  cmpPair (x , y) (x₁ , y₁) | less x<x₁    = less    (fst< x<x₁)
  cmpPair (x , y) (x₁ , y₁) | greater x₁<x = greater (fst< x₁<x)
  cmpPair (x , y) (.x , y₁) | equal refl   with compare y y₁
  cmpPair (x₁ , y) (.x₁ , y₁) | equal refl | less y<y₁    = less    (snd< y<y₁)
  cmpPair (x₁ , y) (.x₁ , y₁) | equal refl | greater y₁<y = greater (snd< y₁<y)
  cmpPair (x₁ , y) (.x₁ , .y) | equal refl | equal refl   = equal refl

OrdPair : ∀ {a b} {A : Set a} {B : Set b} {{OrdA : Ord A}} {{OrdB : Ord B}} → Ord (A × B)
OrdPair = record { LessThan = LessPair ; compare = cmpPair }