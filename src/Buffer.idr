module Buffer

import Data.Vect

import SizedStrings
import Lines
import Cursor
import Movement

%default total
%access public

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

private
moveByChar : Buffer v -> Move ByCharacter -> Buffer v
moveByChar (Buffer' lines cursor) movement =
  let newCursor = moveByChar cursor movement
  in Buffer' lines newCursor

private
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

