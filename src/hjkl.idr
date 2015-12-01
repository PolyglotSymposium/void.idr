module hjkl

import Data.Fin
import Data.Vect

import SizedStrings
import Cursor

%default total
%access public

abstract
data Lines : Vect k Nat -> Type where
  Nil : Lines []
  (::) : SizedString n -> Lines v -> Lines (n :: v)

index : {v : Vect k Nat} -> (i : Fin k) -> Lines v -> SizedString (index i v)
index FZ (x :: xs) = x
index (FS y) (x :: xs) = index y xs

line_length_equals_size_from_type : {v : Vect k Nat} -> (i : Fin k) -> (ll : Lines v) -> 
                                    length (index i ll) = index i v
line_length_equals_size_from_type FZ [] impossible
line_length_equals_size_from_type (FS _) [] impossible
line_length_equals_size_from_type FZ (_ :: _) = Refl
line_length_equals_size_from_type (FS _) (_ :: _) = Refl

vectSizeVector : Vect k String -> Vect k Nat
vectSizeVector = map length

readFromVect : (v : Vect k String) -> Lines (vectSizeVector v)
readFromVect [] = []
readFromVect (x :: xs) = sizeString x :: readFromVect xs

listSizeVector : (xs : List String) -> Vect (length xs) Nat
listSizeVector xs = vectSizeVector $ fromList xs

readFromList : (xs : List String) -> Lines (listSizeVector xs)
readFromList xs = readFromVect $ fromList xs

writeLinesToList : Lines v -> List String
writeLinesToList [] = []
writeLinesToList (l :: ls) = cast l :: writeLinesToList ls

abstract
data Buffer : Vect (S k) Nat -> Type where
  Buffer' : {v : Vect (S k) Nat} ->
            (ls : Lines v) ->
            (cursor : Cursor v) ->
            Buffer v

%name Buffer buffer

emptyBuffer : Buffer [Z]
emptyBuffer = Buffer' [sizeString ""] emptyBufferCursor

bufferTypeFromStrings : (xs : List String) -> Type
bufferTypeFromStrings [] = Buffer [Z]
bufferTypeFromStrings (x :: xs) = Buffer $ listSizeVector (x :: xs)

readIntoBuffer : (xs: List String) -> bufferTypeFromStrings xs
readIntoBuffer [] = emptyBuffer
readIntoBuffer (x :: xs) = Buffer' (readFromList $ x :: xs) zeroRowCursor

writeToList : Buffer v -> List String
writeToList (Buffer' l _) = writeLinesToList l

moveByChar : Buffer v -> Move ByCharacter -> Buffer v
moveByChar (Buffer' lines cursor) movement =
  let newCursor = moveByChar cursor movement
  in Buffer' lines newCursor

moveByLine : Buffer v -> Move ByLine -> Buffer v
moveByLine (Buffer' lines cursor) movement =
  Buffer' lines (moveByLine cursor movement)

move : Buffer v -> Move by -> Buffer v
move {by = ByCharacter} = moveByChar
move {by = ByLine} = moveByLine

charUnderCursor : Buffer v -> Maybe Char
charUnderCursor (Buffer' lines cursor) =
  let line = index (currentRowIndex cursor) lines
      maybeColIndex = currentColumnIndex cursor
  in map (strIndex line) maybeColIndex

h : Nat -> Move ByCharacter
h x = Backward x

j : Nat -> Move ByLine
j x = Forward x

l : Nat -> Move ByCharacter
l x = Forward x

k : Nat -> Move ByLine
k x = Backward x

