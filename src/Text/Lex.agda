module Text.Lex where

open import Prelude

record TokenDFA {s} (A : Set) (Tok : Set) : Set (lsuc s) where
  field
    State   : Set s
    initial : State
    accept  : State → Maybe Tok
    consume : A → State → Maybe State

instance
  FunctorTokenDFA : ∀ {s} {A : Set} → Functor (TokenDFA {s = s} A)
  TokenDFA.State   (fmap {{FunctorTokenDFA}} f dfa) = TokenDFA.State dfa
  TokenDFA.initial (fmap {{FunctorTokenDFA}} f dfa) = TokenDFA.initial dfa
  TokenDFA.accept  (fmap {{FunctorTokenDFA}} f dfa) s = f <$> TokenDFA.accept dfa s
  TokenDFA.consume (fmap {{FunctorTokenDFA}} f dfa) = TokenDFA.consume dfa

keywordToken : {A : Set} {{EqA : Eq A}} → List A → TokenDFA A ⊤
TokenDFA.State   (keywordToken {A = A} kw)    = List A
TokenDFA.initial (keywordToken kw)            = kw
TokenDFA.accept  (keywordToken kw) []         = just _
TokenDFA.accept  (keywordToken kw) (_ ∷ _)    = nothing
TokenDFA.consume (keywordToken kw) _ []       = nothing
TokenDFA.consume (keywordToken kw) y (x ∷ xs) = ifYes (x == y) then just xs else nothing

matchToken : ∀ {A : Set} (p : A → Bool) → TokenDFA A (List (Σ A (IsTrue ∘ p)))
TokenDFA.State (matchToken {A = A} p) = List (Σ A (IsTrue ∘ p))
TokenDFA.initial (matchToken _)       = []
TokenDFA.accept  (matchToken _) xs    = just (reverse xs)
TokenDFA.consume (matchToken p) x xs  = if′ p x then just ((x , it) ∷ xs) else nothing

natToken : TokenDFA Char Nat
natToken = pNat <$> matchToken isDigit
  where pNat = foldl (λ { n (d , _) → 10 * n + (charToNat d - charToNat '0') }) 0

identToken : ∀ {A : Set} → (A → Bool) → (A → Bool) → TokenDFA A (List A)
TokenDFA.State   (identToken {A = A} _ _) = Maybe (List A)
TokenDFA.initial (identToken _ _) = nothing
TokenDFA.accept  (identToken _ _) = fmap reverse
TokenDFA.consume (identToken first _) x nothing   = if first x then just (just [ x ])    else nothing
TokenDFA.consume (identToken _ then)  x (just xs) = if then  x then just (just (x ∷ xs)) else nothing

module _ {s : Level} {A Tok : Set} where
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
      case accepts active of λ where
        []      → []  -- not quite right if there are active DFAs
        (t ∷ _) → [ t ]
    tokenize-loop idle [] (x ∷ xs) =
      flip uncurry (partitionMap (feed x) (map init idle)) λ where
        idle₁ []      → []
        idle₁ active₁ → tokenize-loop idle₁ active₁ xs
    tokenize-loop idle active (x ∷ xs) =
      flip uncurry (partitionMap (feed x) active) λ where
        idle₁ [] →
          case accepts active of λ where
            []      → []
            (t ∷ _) →
              flip uncurry (partitionMap (feed x) (map init (idle ++ idle₁))) λ where
                _ []          → t ∷ []
                idle₂ active₂ → t List.∷ tokenize-loop idle₂ active₂ xs
        idle₁ active₁ → tokenize-loop (idle ++ idle₁) active₁ xs

  tokenize : List (TokenDFA {s = s} A Tok) → List A → List Tok
  tokenize dfas xs = tokenize-loop dfas [] xs
