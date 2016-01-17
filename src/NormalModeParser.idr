module NormalModeParser

import Keys

%default total
%access public

data Token = Register KeyChord
           | Multiplier Nat
           | KeyChordT KeyChord

parseMultiplier : Digit -> List KeyChord -> (Nat, List KeyChord)
parseMultiplier digit keycs = 
  let (digitKeys, keycs') = span isDigit keycs
      digits = reverse $ catMaybes $ map toDigit digitKeys
      n = foldr (\d,acc => acc*10+cast d) (cast digit) digits
  in (n, keycs')

private
parseOne : List KeyChord -> (Maybe Token, List KeyChord)
parseOne [] = (Nothing, [])
parseOne ((KC SingleQuote Shift _ _ _ _) :: (keyc :: keycs)) = (Just $ Register keyc, keycs)
parseOne ((KC (DigitKey digit) NoShift _ _ _ _) :: keycs) =
  let (n, keycs') = parseMultiplier digit keycs
  in (Just $ Multiplier n, keycs')
parseOne (keyc :: keycs) = (Just $ KeyChordT keyc, keycs)

parse : List KeyChord -> List Token
parse [] = []
parse (x :: xs) = []
