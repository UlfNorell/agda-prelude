
module Text.Lex where

open import Prelude
open import Data.List

record TokenDFA {a t s} (A : Set a) (Tok : Set t) : Set (t ⊔ a ⊔ lsuc s) where
  field
    State   : Set s
    initial : State
    accept  : State → Maybe Tok
    consume : A → State → Maybe State

FunctorTokenDFA : ∀ {a t s} {A : Set a} → Functor (TokenDFA {t = t} {s = s} A)
FunctorTokenDFA =
  record { fmap = λ f dfa →
    record { State   = TokenDFA.State dfa
           ; initial = TokenDFA.initial dfa
           ; accept  = λ s → f <$> TokenDFA.accept dfa s
           ; consume = TokenDFA.consume dfa
           }
  }

keywordToken : ∀ {a} {A : Set a} {{EqA : Eq A}} → List A → TokenDFA A ⊤
keywordToken {A = A} kw =
  record { State   = List A
         ; initial = kw
         ; accept  = λ s → if null s then just _ else nothing
         ; consume = consume }
  where
    consume : A → List A → Maybe (List A)
    consume y []       = nothing
    consume y (x ∷ xs) = ifYes (x == y) then just xs else nothing

matchToken : ∀ {a} {A : Set a} (p : A → Bool) → TokenDFA A (List (Σ A (IsTrue ∘ p)))
matchToken {A = A} p =
  record { State   = List (Σ A (IsTrue ∘ p))
         ; initial = []
         ; accept  = λ xs → just (reverse xs)
         ; consume = λ x xs → if′ p x then just ((x , ⋯) ∷ xs) else nothing
         }

natToken : TokenDFA Char Nat
natToken = parseNat <$> matchToken isDigit
  where parseNat = foldl (λ { n (d , _) → 10 * n + (charToNat d - charToNat '0') }) 0

identToken : ∀ {a} {A : Set a} → (A → Bool) → (A → Bool) → TokenDFA A (List A)
identToken {A = A} first then =
  record { State   = Maybe (List A)
         ; initial = nothing
         ; accept  = fmap reverse
         ; consume = λ { x nothing   → if first x then just (just [ x ])    else nothing
                       ; x (just xs) → if then  x then just (just (x ∷ xs)) else nothing } }

module _ {a t s : Level} {A : Set a} {Tok : Set t} where
  private
    DFA = TokenDFA {s = s} A Tok
    open TokenDFA

    init : DFA → Σ DFA State
    init d = d , initial d

    feed : A → Σ DFA State → Either DFA (Σ DFA State)
    feed x (d , s) = maybe (left d) (right ∘ _,_ d) (consume d x s)

    accepts : List (Σ DFA State) → List Tok
    accepts = concatMap (λ { (d , s) → maybe [] [_] (accept d s) })

    tokenize-loop : List DFA → List (Σ DFA State) → List A → List Tok
    tokenize-loop idle active [] =
      case accepts active of
      λ { []      → []  -- not quite right if there are active DFAs
        ; (t ∷ _) → [ t ]
        }
    tokenize-loop idle active (x ∷ xs) =
      let idle₀   = if null active then []            else idle
          active₀ = if null active then map init idle else active
      in flip uncurry (partitionMap (feed x) active₀) λ idle₁ active₁ →
         case active₁ of
         λ { [] → case accepts active of
                   λ { []      → []
                     ; (t ∷ _) →
                       flip uncurry (partitionMap (feed x) (map init (idle₀ ++ idle₁)))
                       λ { _ [] → t ∷ []
                         ; idle₂ active₂ → t List.∷ tokenize-loop idle₂ active₂ xs
                         }
                     }
           ; _  → tokenize-loop (idle₀ ++ idle₁) active₁ xs
           }

  tokenize : List (TokenDFA {s = s} A Tok) → List A → List Tok
  tokenize dfas xs = tokenize-loop dfas [] xs
