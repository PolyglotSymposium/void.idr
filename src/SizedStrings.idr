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

