{-# OPTIONS -v profile.interactive:10 #-}
module Data.Nat.Prime where

open import Prelude
open import Data.Nat.GCD
open import Data.Nat.Divide
open import Data.Nat.DivMod
open import Data.Nat.Sqrt
open import Data.Nat.Properties
open import Tactic.Nat

Coprime : Nat → Nat → Set
Coprime a b = gcd! a b ≡ 1

data Prime n : Set where
  prime : n > 1 → (∀ k → k Divides n → Either (k ≡ 1) (k ≡ n)) → Prime n

private
  lem : (a b : Nat) → b > 1 → suc a < suc a * b
  lem a .(suc (k + 1)) (diff! k) = auto

data Composite n : Set where
  composite : ∀ a b → a > 1 → b > 1 → a * b ≡ n → Composite n

pattern composite! a b 1<a 1<b = composite a b 1<a 1<b refl

composite-not-prime : ∀ {n} → Composite n → Prime n → ⊥
composite-not-prime (composite! 0 b (diff _ ()) _)
composite-not-prime (composite! (suc a) b sa>1 b>1) (prime _ f) =
  case f (suc a) (divides-mul-l b divides-refl) of λ 
  { (left  sa=1)   → less-antirefl sa>1 (sym sa=1)
  ; (right sa=sab) → less-antirefl (lem a b b>1) sa=sab
  }

data Prime? n : Set where
  yes  : Prime n     → Prime? n
  no   : Composite n → Prime? n
  tiny : LessNat n 2 → Prime? n

private
  less-inv : ∀ {a b} → ¬ LessNat a b → LessNat b (suc a)
  less-inv {a} {b} a≮b with compare a b
  less-inv a≮b | less a<b    = ⊥-elim (a≮b a<b)
  less-inv a≮b | equal refl  = diff! 0
  less-inv a≮b | greater a>b = follows-from a>b

data _∈[_,_] (n a b : Nat) : Set where
  in-range : a ≤ n → n ≤ b → n ∈[ a , b ]

empty-range : ∀ {n a b} → a > b → ¬ (n ∈[ a , b ])
empty-range a>b (in-range a≤n n≤b) = less-not-geq a>b (a≤n ⟨≤⟩ n≤b)

below-range : ∀ {n a b} → n < a → ¬ (n ∈[ a , b ])
below-range n<a (in-range a≤n _) = less-not-geq n<a a≤n

range-lower-bound : ∀ {n a b} → n ∈[ a , b ] → a ≤ n
range-lower-bound (in-range a<n _) = a<n

range-upper-bound : ∀ {n a b} → n ∈[ a , b ] → n ≤ b
range-upper-bound (in-range _ n<b) = n<b

singleton-range : ∀ {n a} → n ∈[ a , a ] → a ≡ n
singleton-range (in-range a<n n<a) = leq-antisym a<n n<a

suc-range-r : ∀ {n a b} → n ∈[ a , b ] → n ∈[ a , suc b ]
suc-range-r (in-range a<n n<b) = in-range a<n (follows-from n<b)

suc-range-l : ∀ {n a b} → n ∈[ suc a , b ] → n ∈[ a , b ]
suc-range-l (in-range a<n n<b) = in-range (follows-from a<n) n<b

in-range-l :  ∀ {a b} → a ≤ b → a ∈[ a , b ]
in-range-l a<b = in-range (diff! 0) a<b

in-range-r :  ∀ {a b} → a ≤ b → b ∈[ a , b ]
in-range-r a<b = in-range a<b (diff! 0)

non-zero-range : ∀ {n a b} → n ∈[ suc a , b ] → NonZero n
non-zero-range {zero} {a} (in-range (diff k eq) _) = refute eq
non-zero-range {suc _} _ = _

data _∈[_,_]? k a b : Set where
  inside : k ∈[ a , b ] → k ∈[ a , b ]?
  below  : k < a → k ∈[ a , b ]?
  above  : k > b → k ∈[ a , b ]?

cmp-leq : ∀ a b → Either (a < b) (b ≤ a)
cmp-leq a b with compare a b
cmp-leq a b | less    a<b = left a<b
cmp-leq a b | equal   a=b = right (diff 0 (cong suc a=b))
cmp-leq a b | greater a>b = right (follows-from a>b)

in-range? : ∀ k a b → k ∈[ a , b ]?
in-range? k a b with cmp-leq k a
in-range? k a b | left  k<a = below k<a
in-range? k a b | right k≥a with cmp-leq b k
in-range? k a b | right k≥a | left k>b = above k>b
in-range? k a b | right k≥a | right k≤b = inside (in-range k≥a k≤b)

data FindInRange {ℓ} a b (P : Nat → Set ℓ) : Set ℓ where
  here :  ∀ k → k ∈[ a , b ] →   P k  → FindInRange a b P
  none : (∀ k → k ∈[ a , b ] → ¬ P k) → FindInRange a b P

data FindInRange! {ℓ} a b (P : Nat → Set ℓ) : Set ℓ where
  here :  ∀ k → k ∈[ a , b ] → P k → FindInRange! a b P
  none : FindInRange! a b P

private
  not-first : ∀ {ℓ} {P : Nat → Set ℓ} {a b} →
              ¬ P a → (∀ k → k ∈[ suc a , b ] → ¬ P k) →
              ∀ k → k ∈[ a , b ] → ¬ P k
  not-first {a = a} !pa !pa+ k k∈r pk with compare k a
  not-first !pa !pa+ k k∈r              pk | less    k<a  = below-range k<a k∈r
  not-first !pa !pa+ k k∈r              pk | equal   refl = !pa pk
  not-first !pa !pa+ k (in-range _ k≤b) pk | greater k>a  = !pa+ k (in-range (suc-monotone k>a) k≤b) pk

  find! : ∀ {ℓ} {P : Nat → Set ℓ} a b d → d + a ≡ suc b → (∀ k → Dec (P k)) → FindInRange! a b P
  find! a b  zero   eq check = none
  find! a b (suc d) eq check with check a
  find! a b (suc d) eq check | yes pa = here a (in-range-l (diff d (sym eq))) pa
  find! a b (suc d) eq check | no !pa with find! (suc a) b d (follows-from eq) check
  find! a b (suc d) eq check | no !pa | here k k∈sab pk = here k (suc-range-l k∈sab) pk
  find! a b (suc d) eq check | no !pa | none = none

  not-found-in-range : ∀ {ℓ} {P : Nat → Set ℓ} a b d (eq : d + a ≡ suc b) (check : ∀ k → Dec (P k)) →
                         find! a b d eq check ≡ none → ∀ k → k ∈[ a , b ] → ¬ P k
  not-found-in-range a b zero    eq check prf k k∈ab pk = empty-range (diff 0 eq) k∈ab
  not-found-in-range a b (suc d) eq check prf k (in-range a<k k<b) pk with check a
  not-found-in-range a b (suc d) eq check ()  k (in-range a<k k<b) pk | yes pa
  not-found-in-range a b (suc d) eq check prf k (in-range a<k k<b) pk | no !pa
    with find! (suc a) b d (follows-from eq) check | not-found-in-range (suc a) b d (follows-from eq) check
  not-found-in-range a b (suc d) eq check ()  k (in-range a<k k<b) pk | no !pa | here _ _ _ | rec
  not-found-in-range a b (suc d) eq check prf k (in-range a<k k<b) pk | no !pa | none       | rec =
    not-first !pa (rec refl) k (in-range a<k k<b) pk

  find : ∀ {ℓ} {P : Nat → Set ℓ} a b d → d + a ≡ suc b → (∀ k → Dec (P k)) → FindInRange a b P
  find a b d eq check with inspect (find! a b d eq check)
  ... | here k r pk with≡ _ = here k r pk
  ... | none with≡ prf      = none (not-found-in-range a b d eq check prf)

findInRange : ∀ {ℓ} {P : Nat → Set ℓ} a b → (∀ k → Dec (P k)) → FindInRange a b P
findInRange a  b check with compare a b
findInRange a ._ check | less (diff! k) = find a _ (2 + k) refl check
findInRange a .a check | equal   refl   = find a _ 1 refl check
findInRange a  b check | greater gt     = none (λ k k∈ab _ → empty-range gt k∈ab)

--- Reducing the required search space to 2..√a ---

private
  lem-less : ∀ {n r d q} → r ^ 2 ≥ n →
        q * d ≡ n → r < d → suc r ≤ q → ⊥
  lem-less (diff k eq) refl (diff j refl) (diff! i) = refute eq

  non-zero-less : ∀ {a} {{_ : NonZero a}} → 0 < a
  non-zero-less {0} {{}}
  non-zero-less {suc a} = diff a auto

  div-unique : ∀ q {a b} {{_ : NonZero b}} → q * b ≡ a → a div b ≡ q
  div-unique q {a} {b} eq = quot-unique (qr (a div b) (a mod b) (mod-less b a) (divmod-sound b a))
                                        (qr q 0 non-zero-less (follows-from eq))

  divide-smaller : ∀ n r d {{_ : NonZero d}} → n ≤ r ^ 2 → d Divides n → d > r → n div d ≤ r
  divide-smaller n r d n<r² (factor q eq) d>r =
    let n/d=q : n div d ≡ q
        n/d=q = div-unique q eq
    in less-raa (lem-less n<r² (cong (_* d) n/d=q ⟨≡⟩ eq) d>r)

  divide-bigger : ∀ n k {{_ : NonZero k}} → k < n → k Divides n → n div k ≥ 2
  divide-bigger ._ k (diff! k₁) (factor zero eq) = refute eq
  divide-bigger n  k k<n (factor 1 eq) = ⊥-elim (less-antirefl k<n eq)
  divide-bigger n  k k<n (factor (suc (suc q)) eq) =
    transport (2 ≤_) (sym $ div-unique (2 + q) eq) auto

  up-to-root : ∀ r n → r ≤ n → r ^ 2 ≥ suc n → FindInRange 2 r (_Divides suc n) → FindInRange 2 n (_Divides suc n)
  up-to-root r n r<n r²>n (none k∤sn) =
    none λ k k∈2n k|sn → erase-⊥ $
    case in-range? k 2 r of λ
    { (inside k∈2r) → k∤sn k k∈2r k|sn
    ; (below  k<2)  → less-not-geq k<2 (range-lower-bound k∈2n)
    ; (above  k>r)  →
      let k≠0 : NonZero k
          k≠0 = non-zero-range k∈2n
          hi : suc n div k ≤ r
          hi = divide-smaller (suc n) r k r²>n k|sn k>r
          lo : suc n div k ≥ 2
          lo = divide-bigger (suc n) k (range-upper-bound k∈2n) k|sn
      in k∤sn (suc n div k) (in-range lo hi) (factor k (follows-from (div-divides k|sn)))
    }
  up-to-root 0 _ _ _ (here k k∈⊥ _) = ⊥-elim (empty-range (diff! 1) k∈⊥)
  up-to-root (suc r) n r<n r²>n (here k (in-range 2<k k<r) pk) =
    here k (in-range 2<k (k<r ⟨≤⟩ r<n)) pk

private
  is-1-or-n : ∀ {n} → (∀ k → k ∈[ 2 , n ] → k Divides suc n → ⊥) →
                  ∀ k → k Divides suc n → Either (k ≡ 1) (k ≡ suc n)
  is-1-or-n {n} no-div  k (factor q kq=n) with in-range? k 2 n
  is-1-or-n     no-div  k (factor q kq=n) | inside inr = ⊥-elim (no-div k inr (factor q kq=n))
  is-1-or-n     no-div .1 (factor q kq=n) | below (diff! zero) = left refl
  is-1-or-n {n} no-div  k (factor q kq=n) | below (diff (suc k₁) eq) =
    let k=0 : k ≡ 0
        k=0 = plus-zero-r k₁ k (follows-from (sym eq))
    in refute (divides-zero (transport (_Divides suc n) k=0 (factor q kq=n)))
  is-1-or-n {n} no-div  k (factor q kq=n) | above  k>n =
    right (leq-antisym (divides-less (factor q kq=n)) (follows-from k>n))

  lem₂ : ∀ {n d} q → q * d ≡ suc n → d < suc n → q > 1
  lem₂ 0 eq d≤n = refute eq
  lem₂ 1 eq d≤n = ⊥-elim (less-antirefl d≤n eq)
  lem₂ (suc (suc q)) eq d≤n = auto

  two-is-prime : ∀ k → k Divides 2 → Either (k ≡ 1) (k ≡ 2)
  two-is-prime k k|2 with divides-less k|2
  two-is-prime 0 (factor q eq) | k≤2 = refute eq
  two-is-prime 1 k|2 | k≤2 = left refl
  two-is-prime 2 k|2 | k≤2 = right refl
  two-is-prime (suc (suc (suc k))) k|2 | diff k₁ eq = refute eq

  isPrimeAux : ∀ n → Comparison _<_ 2 n → Prime? n
  isPrimeAux 0 _ = tiny (diff! 1)
  isPrimeAux 1 _ = tiny (diff! 0)
  isPrimeAux 2 _ = yes (prime (diff! 0) two-is-prime)
  isPrimeAux (suc (suc (suc n))) (greater (diff k eq)) = refute eq
  isPrimeAux (suc (suc (suc _))) (equal ())
  isPrimeAux (suc n) (less n>2) with sqrt (suc n) | sqrt-less _ n>2
  ... | root r r²<n sr²>n | r<n with up-to-root (suc r) n r<n (follows-from sr²>n) $ findInRange 2 (suc r) (λ k → k divides? suc n)
  ...   | none p = yes (prime (follows-from n>2) (is-1-or-n p))
  ...   | here d (in-range 2≤d d≤n) (factor q eq) =
    no (composite d q (suc-monotoneʳ 2≤d) (lem₂ q eq d≤n) (follows-from eq))

isPrime : ∀ n → Prime? n
isPrime n = isPrimeAux n (compare 2 n)

isPrime! : Nat → Bool
isPrime! n with isPrime n
... | yes  _ = true
... | no   _ = false
... | tiny _ = false

testPrimeProof : Nat → String
testPrimeProof n with isPrime n
... | tiny _ = show n & " is tiny"
... | no (composite a b _ _ _) = show a & " * " & show b
... | yes (prime _ f) with f n divides-refl
testPrimeProof .1 | yes (prime x f) | left  refl = "n ≡ 1"
testPrimeProof  n | yes (prime x f) | right refl = "n ≡ " & show n

-- Benchmarking

-- Todo: test only odd numbers

--   Composite
--       5.0s    + isPrime 1927   (41 * 47)
--        40ms   recurse from below
--       5.2s    + isPrime (1021 * 1021)
--       0.2s    remove range argument from check
--       0.8s    + isPrime (3581 * 3581)

--   Prime (no proof)
--       2.3s    + isPrime! 1021
--       5.0s    recurse from below
--       0.1s    remove range argument from check
--       0.7s    + isPrime! 3581

--   Prime (run proof: cheap because we're not actually running the (negative) function computed by find)
--       0.7s    + testPrimeProof 3581

--   Prime (print proof)
--       1.8s    + isPrime 83
--       3.4s    recurse from below
--       2.6s    remove range argument from check
--       0.1s    split negative proof into separate function
--       0.6s    + isPrime 3581
--       0.2s    only check up to sqrt
--       0.7s    + isPrime 12823607
--       2.3s    + isPrime 234576373
