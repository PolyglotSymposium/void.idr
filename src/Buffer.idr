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
readIntoBuffer (x :: xs) = Buffer' (readFromList $ x :: xs) zeroColumnCursor

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

bufferTypeFromLineDelete : {size : Vect (S k) Nat} -> Buffer size -> Type
bufferTypeFromLineDelete {k = Z} _ = Buffer [Z]
bufferTypeFromLineDelete {k = (S _)} {size} (Buffer' _ cursor) =
  Buffer (deleteAt (currentRowIndex cursor) size)

deleteLine : {size : Vect (S k) Nat} -> (b : Buffer size) -> bufferTypeFromLineDelete b
deleteLine {k = Z} _ = emptyBuffer
deleteLine {k = (S _)} (Buffer' ls cursor) =
  let newLines = deleteLine (currentRowIndex cursor) ls
      newCursor = deleteLine cursor
  in Buffer' newLines newCursor

bufferTypeFromLineInsert : {size : Vect (S k) Nat} -> Buffer size -> Type
bufferTypeFromLineInsert {size} (Buffer' _ cursor) =
  Buffer (insertAt (weaken $ currentRowIndex cursor) Z size)

insertLineAbove : (b : Buffer size) -> bufferTypeFromLineInsert b
insertLineAbove (Buffer' ls cursor) =
  let newLines = insertLine (weaken $ currentRowIndex cursor) empty ls
      newCursor = insertLine Z cursor
  in Buffer' newLines newCursor
