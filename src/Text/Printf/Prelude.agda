
module Text.Printf.Prelude where

open import Prelude hiding (parseNat)
open import Builtin.Float

private
  data Padding : Set where
    noPad     : Padding
    lPad rPad : Nat → Padding

  record Flags : Set where
    field
      padding   : Padding
      padChar   : Char
      alternate : Bool
      precision : Maybe Nat

  defaultFlags : Flags
  Flags.padding   defaultFlags = noPad
  Flags.padChar   defaultFlags = ' '
  Flags.alternate defaultFlags = false
  Flags.precision defaultFlags = nothing

  data Format : Set where
    natArg    : Flags → Format
    strArg    : Flags → Format
    ustrArg   : Flags → Format
    floatArg  : Flags → Format
    charArg   : Format
    hexArg    : Bool → Flags → Format
    litString : String → Format
    badFormat : String → Format

data BadFormat (s : String) : Set where

private
  BadFormat′ : String → Set
  BadFormat′ "" = ⊥
  BadFormat′ s = BadFormat s

private
  consLit : String → List Format → List Format
  consLit s (litString s′ ∷ fmt) = litString (s & s′) ∷ fmt
  consLit s fmt = litString s ∷ fmt

private
  parseFormat : List Char → List Format
  parseFormatWithFlags : Flags → List Char → List Format

  parseNat′ : (Nat → Flags) → Nat → List Char → List Format
  parseNat′ flags n [] = parseFormatWithFlags (flags n) []
  parseNat′ flags n (c ∷ s) =
    if isDigit c then parseNat′ flags (n * 10 + charToNat c - charToNat '0') s
                 else parseFormatWithFlags (flags n) (c ∷ s)

  parseNat : (Nat → Flags) → List Char → List Format
  parseNat p s = parseNat′ p 0 s

  parsePadding : Flags → List Char → List Format
  parsePadding f [] = parseFormatWithFlags f []
  parsePadding f ('-' ∷ c ∷ s) =
    if isDigit c then parseNat (λ n → record f { padding = rPad n }) (c ∷ s)
                 else badFormat (packString ('-' ∷ c ∷ [])) ∷ parseFormat s
  parsePadding f ('0' ∷ s) = parsePadding (record f { padChar = '0' }) s
  parsePadding f ('.' ∷ c ∷ s) =
    if isDigit c then parseNat (λ n → record f { precision = just n }) (c ∷ s)
                 else badFormat (packString ('.' ∷ c ∷ [])) ∷ parseFormat s
  parsePadding f (c ∷ s) =
    if isDigit c then parseNat (λ n → record f { padding = lPad n }) (c ∷ s)
                 else parseFormatWithFlags f (c ∷ s)

  parseFlags : Flags → List Char → List Format
  parseFlags f ('#' ∷ s) = parseFlags (record f { alternate = true }) s
  parseFlags f s = parsePadding f s

  parseFormatWithFlags f [] = badFormat "" ∷ []
  parseFormatWithFlags f ('d' ∷ s) = natArg f ∷ parseFormat s
  parseFormatWithFlags f ('x' ∷ s) = hexArg false f ∷ parseFormat s
  parseFormatWithFlags f ('X' ∷ s) = hexArg true  f ∷ parseFormat s
  parseFormatWithFlags f ('c' ∷ s) = charArg ∷ parseFormat s
  parseFormatWithFlags f ('s' ∷ s) = strArg f ∷ parseFormat s
  parseFormatWithFlags f ('S' ∷ s) = ustrArg f ∷ parseFormat s
  parseFormatWithFlags f ('f' ∷ s) = floatArg f ∷ parseFormat s
  parseFormatWithFlags f ('%' ∷ s) = consLit "%" $ parseFormat s
  parseFormatWithFlags f ( c  ∷ s) = badFormat (packString ('%' ∷ c ∷ [])) ∷ parseFormat s

  parseFormat [] = []
  parseFormat ('%' ∷ fmt) = parseFlags defaultFlags fmt
  parseFormat (c   ∷ fmt) = consLit (packString [ c ]) $ parseFormat fmt

private
  pad : (String → String → String) → Char → Nat → String → String
  pad _+_ c n s =
    case n - length (unpackString s) of
    λ { 0 → s ; d → packString (replicate d c) + s}

  padLeft padRight : Char → Nat → String → String
  padLeft  = pad _&_
  padRight = pad (flip _&_)

  hexDigit : Char → Nat → String
  hexDigit a n = if n <? 10 then packString [ natToChar (n + charToNat '0') ]
                            else packString [ natToChar (n - 10 + charToNat a) ]

  {-# TERMINATING #-}
  showHex′ : Char → Nat → String
  showHex′ _ 0 = ""
  showHex′ a n = showHex′ a (n div 16) & hexDigit a (n mod 16)

  add0x : Flags → String → String
  add0x flags s = if Flags.alternate flags then "0x" & s else s

  pad0 : Flags → String → String
  pad0 flags s =
    let c = Flags.padChar flags in
    ifYes c == ' ' then s else
    case Flags.padding flags of
    λ { noPad → s ; (lPad n) → padLeft c (n - 2) s ; (rPad _) → s }

  showHex : Flags → Bool → Nat → String
  showHex f _ 0 = add0x f $ pad0 f $ "0"
  showHex f u n = add0x f $ pad0 f $ showHex′ (if u then 'A' else 'a') n

  showFrac : Nat → Float → String
  showFrac 0       _ = ""
  showFrac 1       x = show (round (10 * x))
  showFrac (suc p) x = show n & showFrac p (x′ - intToFloat n)
    where x′ = 10 * x
          n  = floor x′

  showPosFloat : Flags → Float → String
  showPosFloat f x =
    case Flags.precision f of λ
    { nothing  → show x
    ; (just 0) → show (floor x)
    ; (just p) → show (floor x) & "." & showFrac p (x - intToFloat (floor x))
    }

  showFloat : Flags → Float → String
  showFloat f x with x <? 0.0
  ... | true = "-" & showPosFloat f (negate x)
  ... | false = showPosFloat f x

  withPad : Flags → String → ShowS
  withPad flags s =
    let c = Flags.padChar flags in
    case Flags.padding flags of
    λ { noPad → showString s
      ; (lPad n) → showString (padLeft  c n s)
      ; (rPad n) → showString (padRight c n s)
      }

private
  Printf′ : List Format → Set
  Printf′ []                  = String
  Printf′ (natArg _    ∷ fmt) = Nat → Printf′ fmt
  Printf′ (hexArg _ _  ∷ fmt) = Nat → Printf′ fmt
  Printf′ (strArg _    ∷ fmt) = String → Printf′ fmt
  Printf′ (ustrArg _   ∷ fmt) = List Char → Printf′ fmt
  Printf′ (charArg     ∷ fmt) = Char → Printf′ fmt
  Printf′ (floatArg _  ∷ fmt) = Float → Printf′ fmt
  Printf′ (litString _ ∷ fmt) = Printf′ fmt
  Printf′ (badFormat e ∷ fmt) = BadFormat′ e → Printf′ fmt

  printf′ : (fmt : List Format) → ShowS → Printf′ fmt
  printf′ [] acc = acc ""
  printf′ (natArg p    ∷ fmt) acc n = printf′ fmt (acc ∘ withPad p (show n))
  printf′ (hexArg u p  ∷ fmt) acc n = printf′ fmt (acc ∘ withPad p (showHex p u n))
  printf′ (strArg p    ∷ fmt) acc s = printf′ fmt (acc ∘ withPad p s)
  printf′ (ustrArg p   ∷ fmt) acc s = printf′ fmt (acc ∘ withPad p (packString s))
  printf′ (floatArg p  ∷ fmt) acc x = printf′ fmt (acc ∘ withPad p (showFloat p x))
  printf′ (charArg     ∷ fmt) acc c = printf′ fmt (acc ∘ showString (packString [ c ]))
  printf′ (litString s ∷ fmt) acc   = printf′ fmt (acc ∘ showString s)
  printf′ (badFormat _ ∷ fmt) acc _ = printf′ fmt acc

Printf : String → Set
Printf = Printf′ ∘ parseFormat ∘ unpackString

printf : (fmt : String) → Printf fmt
printf fmt = printf′ (parseFormat $ unpackString fmt) id
