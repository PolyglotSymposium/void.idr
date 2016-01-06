module SizedStrings

import Data.Fin

%default total
%access public

||| A string with length encoded in the type
||| Need to investigate this PR:
||| https://github.com/idris-lang/Idris-dev/pull/2628
||| It may be that his work, if completed, would make this module obsolete!!
abstract data SizedString : Nat -> Type where
  SizedString' : (n : Nat) -> (s : String) -> SizedString n

%name SizedString str

||| This is the only was to create a SizedString
sizeString : (s : String) -> SizedString (length s)
sizeString s = SizedString' (length s) s

empty : SizedString Z
empty = sizeString ""

||| Length of the string, equal to the Nat carried in the type
length : SizedString n -> Nat
length {n} _ = n

length_is_embedded_in_type : (str : SizedString n) -> length str = n
length_is_embedded_in_type str = Refl

||| Typesafe way to get a character from a string at the specified index.
||| The order of arguments is patterned after Strings.strIndex, not, say, List.index.
||| Under the covers it does an assert_total call because the underlying
||| String.strIndex function is partial. However, we know this is safe as long
||| as SizedString is only created via the sizeString function from this module.
strIndex : SizedString n -> Fin n -> Char
strIndex (SizedString' _ s) x =
  assert_total $ strIndex s $ cast $ finToNat x

instance Cast (SizedString n) String where
  cast (SizedString' _ s) = s

replaceAt : Fin (S n) -> Char -> SizedString (S n) -> SizedString (S n)
replaceAt {n} i c (SizedString' _ str) =
  let charsBefore = finToNat i
      indexAfter = S charsBefore
      size = S n
      firstChunk = substr 0 charsBefore str
      secondChunk = substr indexAfter size str
  in SizedString' size $ firstChunk ++ (strCons c $ secondChunk)

(++) : SizedString n -> SizedString m -> SizedString (n + m)
(SizedString' _ str1) ++ (SizedString' _ str2) = SizedString' _ $ str1 ++ str2

insertAfter : SizedString n -> (idx : Maybe (Fin n)) -> SizedString m -> SizedString (n + m)
insertAfter str1 Nothing str2 = str1 ++ str2
insertAfter (SizedString' n str) (Just x) (SizedString' _ infixStr) =
  let idx = S $ finToNat x
      prefixStr = substr 0 idx str
      postfixStr = substr idx n str
  in SizedString' _ $ prefixStr ++ infixStr ++ postfixStr

