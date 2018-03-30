
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

infixr 9 _∘_
_∘_ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c}
        (f : ∀ {x} (y : B x) → C x y) (g : ∀ x → B x) →
        ∀ x → C x (g x)
(f ∘ g) x = f (g x)
{-# INLINE _∘_ #-}

infixr 9 _∘′_
_∘′_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
         (B → C) → (A → B) → (A → C)
f ∘′ g = f ∘ g
{-# INLINE _∘′_ #-}

infixr -20 _$_ _$′_
infixr 0 case_of_ case_return_of_
_$_ : ∀ {a b} {A : Set a} {B : A → Set b} → (∀ x → B x) → ∀ x → B x
f $ x = f x

_$′_ : ∀ {a b}{A : Set a} {B : Set b} → (A → B) → A → B
f $′ x = f x

case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x

case₂_,_of_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} → A → B → (A → B → C) → C
case₂ x , y of f = f x y

case₃_,_,_of_ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} → A → B → C → (A → B → C → D) → D
case₃ x , y , z of f = f x y z

case₄_,_,_,_of_ : ∀ {a b c d e} {A : Set a} {B : Set b} {C : Set c} {D : Set d} {E : Set e} →
                A → B → C → D → (A → B → C → D → E) → E
case₄ x , y , z , w of f = f x y z w

case_return_of_ : ∀ {a b} {A : Set a} (x : A) (B : A → Set b) → (∀ x → B x) → B x
case x return B of f = f x

infixr 0 letSyntax
syntax letSyntax e (λ x → b) = let[ x := e ] b
letSyntax : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
letSyntax x f = f x

{-# INLINE _$_ #-}
{-# INLINE _$′_ #-}
{-# INLINE case_of_ #-}
{-# INLINE case₂_,_of_ #-}
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

asInstance : ∀ {a b} {A : Set a} {B : A → Set b} (x : A) → (∀ {{x}} → B x) → B x
asInstance x f = f {{x}}
{-# INLINE asInstance #-}

record Instance {a} (A : Set a) : Set a where
  constructor !
  field {{x}} : A

mkInstance : ∀ {a} {A : Set a} → A → Instance A
mkInstance x = ! {{x}}
{-# INLINE mkInstance #-}

-- Can be used to force normalisation at compile time.
static : ∀ {a} {A : Set a} → A → A
static x = x
{-# STATIC static #-}
