
module Prelude.Function where

id : ∀ {a} {A : Set a} → A → A
id x = x

const : ∀ {a b} {A : Set a} {B : Set b} → A → B → A
const x _ = x

flip : ∀ {a b c} {A : Set a} {B : Set b} {C : A → B → Set c} → (∀ x y → C x y) → ∀ y x → C x y
flip f x y = f y x

infixl 9 _∘_
_∘_ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c}
        (f : ∀ {x} (y : B x) → C x y) (g : ∀ x → B x) →
        ∀ x → C x (g x)
(f ∘ g) x = f (g x)

infixr 0 _$_ _$′_ case_of_
_$_ : ∀ {a b} {A : Set a} {B : A → Set b} → (∀ x → B x) → ∀ x → B x
f $ x = f x

_$′_ : ∀ {a b}{A : Set a} {B : Set b} → (A → B) → A → B
f $′ x = f x

case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x

infixl 8 _on_
_on_ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : ∀ x y → B x → B y → Set c} →
         (∀ {x y} (z : B x) (w : B y) → C x y z w) → (f : ∀ x → B x) → ∀ x y →
         C x y (f x) (f y)
h on f = λ x y → h (f x) (f y)

⋯ : ∀ {a} {A : Set a} {{x : A}} → A
⋯ {{x}} = x
