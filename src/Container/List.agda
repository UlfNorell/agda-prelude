
module Container.List where

open import Prelude

infixr 5 _∷_
data All {a b} {A : Set a} (P : A → Set b) : List A → Set (a ⊔ b) where
  []  : All P []
  _∷_ : ∀ {x xs} (p : P x) (ps : All P xs) → All P (x ∷ xs)

data Any {a b} {A : Set a} (P : A → Set b) : List A → Set (a ⊔ b) where
  instance
    zero : ∀ {x xs} (p : P x) → Any P (x ∷ xs)
    suc  : ∀ {x xs} (i : Any P xs) → Any P (x ∷ xs)

pattern zero! = zero refl

-- Literal overloading for Any
module _ {a b} {A : Set a} {P : A → Set b} where
  private
    AnyConstraint : List A → Nat → Set (a ⊔ b)
    AnyConstraint []        _      = ⊥′
    AnyConstraint (x ∷  _)  zero   = ⊤′ {a} × P x   -- hack to line up levels
    AnyConstraint (_ ∷ xs) (suc i) = AnyConstraint xs i

    natToIx : ∀ (xs : List A) n → {{_ : AnyConstraint xs n}} → Any P xs
    natToIx [] n {{}}
    natToIx (x ∷ xs)  zero {{_ , px}} = zero px
    natToIx (x ∷ xs) (suc n) = suc (natToIx xs n)

  instance
    NumberAny : ∀ {xs} → Number (Any P xs)
    Number.Constraint (NumberAny {xs}) = AnyConstraint xs
    fromNat {{NumberAny {xs}}} = natToIx xs

infix 3 _∈_
_∈_ : ∀ {a} {A : Set a} → A → List A → Set a
x ∈ xs = Any (_≡_ x) xs

forgetAny : ∀ {a p} {A : Set a} {P : A → Set p} {xs : List A} → Any P xs → Nat
forgetAny (zero _) = zero
forgetAny (suc  i) = suc (forgetAny i)

lookupAny : ∀ {a b} {A : Set a} {P Q : A → Set b} {xs} → All P xs → Any Q xs → Σ A (λ x → P x × Q x)
lookupAny (p ∷ ps) (zero q) = _ , p , q
lookupAny (p ∷ ps) (suc  i) = lookupAny ps i

lookup∈ : ∀ {a b} {A : Set a} {P : A → Set b} {xs x} → All P xs → x ∈ xs → P x
lookup∈ (p ∷ ps) (zero refl) = p
lookup∈ (p ∷ ps) (suc i)     = lookup∈ ps i

module _ {a b} {A : Set a} {P Q : A → Set b} (f : ∀ {x} → P x → Q x) where
  mapAll : ∀ {xs} → All P xs → All Q xs
  mapAll [] = []
  mapAll (x ∷ xs) = f x ∷ mapAll xs

  mapAny : ∀ {xs} → Any P xs → Any Q xs
  mapAny (zero x) = zero (f x)
  mapAny (suc i)  = suc (mapAny i)

-- Equality --

module _ {a b} {A : Set a} {P : A → Set b} {{EqP : ∀ {x} → Eq (P x)}} where

  private
    z : ∀ {x xs} → P x → Any P (x ∷ xs)
    z = zero

    zero-inj : ∀ {x} {xs : List A} {p q : P x} → Any.zero {xs = xs} p ≡ z q → p ≡ q
    zero-inj refl = refl

    sucAny-inj : ∀ {x xs} {i j : Any P xs} → Any.suc {x = x} i ≡ Any.suc {x = x} j → i ≡ j
    sucAny-inj refl = refl

    cons-inj₁ : ∀ {x xs} {p q : P x} {ps qs : All P xs} → p All.∷ ps ≡ q ∷ qs → p ≡ q
    cons-inj₁ refl = refl

    cons-inj₂ : ∀ {x xs} {p q : P x} {ps qs : All P xs} → p All.∷ ps ≡ q ∷ qs → ps ≡ qs
    cons-inj₂ refl = refl

  instance
    EqAny : ∀ {xs} → Eq (Any P xs)
    _==_ {{EqAny}} (zero p) (zero q) = decEq₁ zero-inj   (p == q)
    _==_ {{EqAny}} (suc i)  (suc j)  = decEq₁ sucAny-inj (i == j)
    _==_ {{EqAny}} (zero _) (suc _)  = no λ ()
    _==_ {{EqAny}} (suc _)  (zero _) = no λ ()

    EqAll : ∀ {xs} → Eq (All P xs)
    _==_ {{EqAll}} []       []       = yes refl
    _==_ {{EqAll}} (x ∷ xs) (y ∷ ys) = decEq₂ cons-inj₁ cons-inj₂ (x == y) (xs == ys)
