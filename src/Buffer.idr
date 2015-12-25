module Buffer

import Data.Vect

import SizedStrings
import Lines
import Cursor
import Movement

%default total
%access public

abstract
data Buffer : Nat -> Type where
  Buffer' : .{size : Vect (S n) Nat} ->
            (ls : Lines size) ->
            (cursor : Cursor n) ->
            Buffer n

%name Buffer buffer

emptyBuffer : Buffer Z
emptyBuffer = Buffer' [empty] zeroCursor

readIntoBuffer : (xs: List String) -> Buffer (pred $ length xs)
readIntoBuffer [] = emptyBuffer
readIntoBuffer (x :: xs) = Buffer' (readFromList $ x :: xs) zeroCursor

writeToList : Buffer n -> List String
writeToList (Buffer' l _) = writeLinesToList l

private
moveByChar : Buffer n -> Move ByCharacter -> Buffer n
moveByChar (Buffer' lines cursor) movement =
  let newCursor = moveByChar movement (length $ index (rowIndex cursor) lines) cursor 
  in Buffer' lines newCursor

private
moveByLine : Buffer n -> Move ByLine -> Buffer n
moveByLine (Buffer' lines cursor) movement =
  Buffer' lines (moveByLine movement cursor)

move : Buffer n -> Move by -> Buffer n
move {by = ByCharacter} = moveByChar
move {by = ByLine} = moveByLine

charUnderCursor : Buffer n -> Maybe Char
charUnderCursor (Buffer' lines cursor) =
  let line = index (rowIndex cursor) lines
      maybeColIndex = columnCursor cursor
  in map (strIndex line) maybeColIndex

deleteLine : Buffer n -> Buffer (pred n)
deleteLine {n = Z} _ = emptyBuffer
deleteLine {n = (S _)} (Buffer' ls cursor) =
  let newLines = deleteLine (rowIndex cursor) ls
      newCursor = deleteLine cursor
  in Buffer' newLines newCursor

insertLineAbove : Buffer n -> Buffer (S n)
insertLineAbove (Buffer' ls cursor) =
  let newLines = insertLine (weaken $ rowIndex cursor) empty ls
      newCursor = insertLineAbove cursor
  in Buffer' newLines newCursor

changeChar : Buffer n -> Char -> Buffer n
changeChar (Buffer' linez cursor) c =
  let row = rowIndex cursor
      column = columnCursor cursor
  in Buffer' (replaceChar row column c linez) cursor

