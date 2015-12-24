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
  Buffer' : {size : Vect (S k) Nat} ->
            (ls : Lines size) ->
            (cursor : Cursor k) ->
            Buffer size

%name Buffer buffer

emptyBuffer : Buffer [Z]
emptyBuffer = Buffer' [sizeString ""] zeroCursor

bufferTypeFromStrings : (xs : List String) -> Type
bufferTypeFromStrings [] = Buffer [Z]
bufferTypeFromStrings (x :: xs) = Buffer $ listSizeVector (x :: xs)

readIntoBuffer : (xs: List String) -> bufferTypeFromStrings xs
readIntoBuffer [] = emptyBuffer
readIntoBuffer (x :: xs) = Buffer' (readFromList $ x :: xs) zeroCursor

writeToList : Buffer v -> List String
writeToList (Buffer' l _) = writeLinesToList l

private
moveByChar : Buffer size -> Move ByCharacter -> Buffer size
moveByChar (Buffer' lines cursor) movement =
  let newCursor = moveByChar movement (index (rowIndex cursor) size) cursor 
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
  let line = index (rowIndex cursor) lines
      maybeColIndex = columnCursor cursor
  in map (strIndex line) maybeColIndex

bufferTypeFromLineDelete : {size : Vect (S k) Nat} -> Buffer size -> Type
bufferTypeFromLineDelete {k = Z} _ = Buffer [Z]
bufferTypeFromLineDelete {k = (S _)} (Buffer' _ cursor) =
  Buffer (deleteAt (rowIndex cursor) size)

deleteLine : {size : Vect (S k) Nat} -> (b : Buffer size) -> bufferTypeFromLineDelete b
deleteLine {k = Z} _ = emptyBuffer
deleteLine {k = (S _)} (Buffer' ls cursor) =
  let newLines = deleteLine (rowIndex cursor) ls
      newCursor = deleteLine cursor
  in Buffer' newLines newCursor

bufferTypeFromLineInsert : {size : Vect (S k) Nat} -> Buffer size -> Type
bufferTypeFromLineInsert (Buffer' _ cursor) =
  Buffer (insertAt (weaken $ rowIndex cursor) Z size)

insertLineAbove : (b : Buffer size) -> bufferTypeFromLineInsert b
insertLineAbove (Buffer' ls cursor) =
  let newLines = insertLine (weaken $ rowIndex cursor) empty ls
      newCursor = insertLineAbove cursor
  in Buffer' newLines newCursor

changeChar : Buffer size -> Char -> Buffer size
changeChar (Buffer' linez cursor) c =
  let row = rowIndex cursor
      column = columnCursor cursor
  in Buffer' (replaceChar row column c linez) cursor

