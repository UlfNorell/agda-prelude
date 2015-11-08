
module Prelude.Function where

id : ∀ {a} {A : Set a} → A → A
id x = x
{-# INLINE id #-}

infixl -10 id
syntax id {A = A} x = x ofType A

const : ∀ {a b} {A : Set a} {B : Set b} → A → B → A
const x _ = x
{-# INLINE const #-}

flip : ∀ {a b c} {A : Set a} {B : Set b} {C : A → B → Set c} → (∀ x y → C x y) → ∀ y x → C x y
flip f x y = f y x
{-# INLINE flip #-}

infixl 9 _∘_
_∘_ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c}
        (f : ∀ {x} (y : B x) → C x y) (g : ∀ x → B x) →
        ∀ x → C x (g x)
(f ∘ g) x = f (g x)
{-# INLINE _∘_ #-}

infixr 0 _$_ _$′_ case_of_ case_return_of_
_$_ : ∀ {a b} {A : Set a} {B : A → Set b} → (∀ x → B x) → ∀ x → B x
f $ x = f x

_$′_ : ∀ {a b}{A : Set a} {B : Set b} → (A → B) → A → B
f $′ x = f x

case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x

case_return_of_ : ∀ {a b} {A : Set a} (x : A) (B : A → Set b) → (∀ x → B x) → B x
case x return B of f = f x

{-# INLINE _$_ #-}
{-# INLINE _$′_ #-}
{-# INLINE case_of_ #-}
{-# INLINE case_return_of_ #-}

infixl 8 _on_
_on_ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : ∀ x y → B x → B y → Set c} →
         (∀ {x y} (z : B x) (w : B y) → C x y z w) → (f : ∀ x → B x) → ∀ x y →
         C x y (f x) (f y)
h on f = λ x y → h (f x) (f y)
{-# INLINE _on_ #-}

it : ∀ {a} {A : Set a} {{x : A}} → A
it {{x}} = x
{-# INLINE it #-}
