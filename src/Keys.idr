module Keys

%default total
%access public

data Digit = Zero | One | Two | Three | Four
           | Five | Six | Seven | Eight | Nine

%name Digit digit

instance Eq Digit where
  Zero == Zero = True
  One == One = True
  Two == Two = True
  Three == Three = True
  Four == Four = True
  Five == Five = True
  Six == Six = True
  Seven == Seven = True
  Eight == Eight = True
  Nine == Nine = True
  _ == _ = False

instance Cast Digit Nat where
  cast Zero = 0
  cast One = 1
  cast Two = 2
  cast Three = 3
  cast Four = 4
  cast Five = 5
  cast Six = 6
  cast Seven = 7
  cast Eight = 8
  cast Nine = 9

data Key = DigitKey Digit
         | A | B | C | D | E | F | G | H | I | J | K | L | M
         | N | O | P | Q | R | S | T | U | V | W | X | Y | Z
         | Backtick
         | Dash
         | EqualSign
         | OpenSquareBracket | CloseSquareBracket
         | Slash | Backslash
         | Tab
         | Semicolon
         | SingleQuote
         | Comma | Period
         | F1 | F2 | F3 | F4 | F5 | F6 | F7 | F8 | F9 | F10 | F11 | F12
         | Escape
         | Insert
         | Delete
         | Backspace
         | Home | End
         | PageUp | PageDown
         | Enter

%name Key key

instance Eq Key where
  (DigitKey x) == (DigitKey y) = x == y
  A == A = True
  B == B = True
  C == C = True
  D == D = True
  E == E = True
  F == F = True
  G == G = True
  H == H = True
  I == I = True
  J == J = True
  K == K = True
  L == L = True
  M == M = True
  N == N = True
  O == O = True
  P == P = True
  Q == Q = True
  R == R = True
  S == S = True
  T == T = True
  U == U = True
  V == V = True
  W == W = True
  X == X = True
  Y == Y = True
  Z == Z = True
  Backtick == Backtick = True
  Dash == Dash = True
  EqualSign == EqualSign = True
  OpenSquareBracket == OpenSquareBracket = True
  CloseSquareBracket == CloseSquareBracket = True
  Slash == Slash = True
  Backslash == Backslash = True
  Tab == Tab = True
  Semicolon == Semicolon = True
  SingleQuote == SingleQuote = True
  Comma == Comma = True
  Period == Period = True
  F1 == F1 = True
  F2 == F2 = True
  F3 == F3 = True
  F4 == F4 = True
  F5 == F5 = True
  F6 == F6 = True
  F7 == F7 = True
  F8 == F8 = True
  F9 == F9 = True
  F10 == F10 = True
  F11 == F11 = True
  F12 == F12 = True
  Escape == Escape = True
  Insert == Insert = True
  Delete == Delete = True
  Backspace == Backspace = True
  Home == Home = True
  End == End = True
  PageUp == PageUp = True
  PageDown == PageDown = True
  Enter == Enter = True
  _ == _ = False

isDigitKey : Key -> Bool
isDigitKey (DigitKey _) = True
isDigitKey _ = False

-- Aliases for readability
Shift : Bool
Shift = True

NoShift : Bool
NoShift = False

record KeyChord where
  constructor KC
  key : Key
  shift : Bool
  alt : Bool
  ctrl : Bool
  fn : Bool
  super : Bool

%name KeyChord keyc

unmod : Key -> KeyChord
unmod key = KC key NoShift False False False False

shifted : Key -> KeyChord
shifted key = record { shift = Shift } $ unmod key

isUnmod : KeyChord -> Bool
isUnmod (KC _ False False False False False) = True
isUnmod _ = False

isDigit : KeyChord -> Bool
isDigit keyc = (isDigitKey . key) keyc && isUnmod keyc

toDigit : KeyChord -> Maybe Digit
toDigit (KC (DigitKey digit) NoShift _ _ _ _) = Just digit
toDigit _ = Nothing

toKey : Char -> Maybe KeyChord
toKey 'a' = Just $ unmod A
toKey 'b' = Just $ unmod B
toKey 'c' = Just $ unmod C
toKey 'd' = Just $ unmod D
toKey 'e' = Just $ unmod E
toKey 'f' = Just $ unmod F
toKey 'g' = Just $ unmod G
toKey 'h' = Just $ unmod H
toKey 'i' = Just $ unmod I
toKey 'j' = Just $ unmod J
toKey 'k' = Just $ unmod K
toKey 'l' = Just $ unmod L
toKey 'm' = Just $ unmod M
toKey 'n' = Just $ unmod N
toKey 'o' = Just $ unmod O
toKey 'p' = Just $ unmod P
toKey 'q' = Just $ unmod Q
toKey 'r' = Just $ unmod R
toKey 's' = Just $ unmod S
toKey 't' = Just $ unmod T
toKey 'u' = Just $ unmod U
toKey 'v' = Just $ unmod V
toKey 'w' = Just $ unmod W
toKey 'x' = Just $ unmod X
toKey 'y' = Just $ unmod Y
toKey 'z' = Just $ unmod Z
toKey 'A' = Just $ shifted A
toKey 'B' = Just $ shifted B
toKey 'C' = Just $ shifted C
toKey 'D' = Just $ shifted D
toKey 'E' = Just $ shifted E
toKey 'F' = Just $ shifted F
toKey 'G' = Just $ shifted G
toKey 'H' = Just $ shifted H
toKey 'I' = Just $ shifted I
toKey 'J' = Just $ shifted J
toKey 'K' = Just $ shifted K
toKey 'L' = Just $ shifted L
toKey 'M' = Just $ shifted M
toKey 'N' = Just $ shifted N
toKey 'O' = Just $ shifted O
toKey 'P' = Just $ shifted P
toKey 'Q' = Just $ shifted Q
toKey 'R' = Just $ shifted R
toKey 'S' = Just $ shifted S
toKey 'T' = Just $ shifted T
toKey 'U' = Just $ shifted U
toKey 'V' = Just $ shifted V
toKey 'W' = Just $ shifted W
toKey 'X' = Just $ shifted X
toKey 'Y' = Just $ shifted Y
toKey 'Z' = Just $ shifted Z
toKey _ = Nothing

toKeys : String -> List KeyChord
toKeys = catMaybes . map toKey . unpack

