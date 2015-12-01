module Cursor

import Data.Fin
import Data.Vect

%default total
%access public

data By =
  ByCharacter
  | ByLine

data Move : By -> Type where
  Backward : {by : By} -> Nat -> Move by
  Forward : {by : By} -> Nat -> Move by

%name Move movement

private
data RowCursor : Nat -> Type where
  EmptyRowCursor : RowCursor Z
  RowCursor' : Fin (S k) -> RowCursor (S k)

private
zeroRowCursor' : (n : Nat) -> RowCursor n
zeroRowCursor' Z = EmptyRowCursor
zeroRowCursor' (S k) = RowCursor' FZ

private
rowCursorToNat : RowCursor n -> Nat
rowCursorToNat EmptyRowCursor = Z
rowCursorToNat (RowCursor' x) = finToNat x

private
rowCursorToMaybeFin : RowCursor n -> Maybe (Fin n)
rowCursorToMaybeFin EmptyRowCursor = Nothing
rowCursorToMaybeFin (RowCursor' x) = Just x

abstract
data Cursor : Vect (S lastRow) Nat -> Type where
  Cursor' : {size : Vect (S lastRow) Nat} ->
            (rowCursor : Fin (S lastRow)) ->
            (colCursor : RowCursor (index rowCursor size)) ->
            (prevColumn : Nat) ->
            Cursor size

emptyBufferCursor : Cursor [Z]
emptyBufferCursor = Cursor' FZ EmptyRowCursor Z

zeroRowCursor : Cursor size
zeroRowCursor {size} = Cursor' FZ (zeroRowCursor' $ index FZ size) Z

currentRowIndex : {size : Vect (S lastRow) Nat} -> Cursor size -> Fin (S lastRow)
currentRowIndex (Cursor' rowIndex _ _) = rowIndex

columnsInLine : Cursor size -> Nat
columnsInLine {size} cursor = index (currentRowIndex cursor) size

currentColumnIndex : (b : Cursor size) -> Maybe (Fin (columnsInLine b))
currentColumnIndex (Cursor' _ colCursor _) = rowCursorToMaybeFin colCursor

private
moveCursorBackward : Fin (S k) -> Nat -> Fin (S k)
moveCursorBackward FZ _ = FZ
moveCursorBackward (FS x) Z = (FS x)
moveCursorBackward (FS x) (S k) = moveCursorBackward (weaken x) k

private
moveCursorForward : Fin (S k) -> Nat -> Fin (S k)
moveCursorForward x Z = x
moveCursorForward x (S k) =
  case strengthen x of
       Left _ => x
       Right x' => moveCursorForward (FS x') k

private
moveByCharInLine : RowCursor n -> Move ByCharacter -> RowCursor n 
moveByCharInLine EmptyRowCursor y = EmptyRowCursor
moveByCharInLine (RowCursor' x) (Backward k) = RowCursor' $ moveCursorBackward x k
moveByCharInLine (RowCursor' x) (Forward k) = RowCursor' $ moveCursorForward x k

moveByChar : Cursor v -> Move ByCharacter -> Cursor v
moveByChar (Cursor' rowCursor columnCursor _) movement =
  let newColCursor = moveByCharInLine columnCursor movement
  in Cursor' rowCursor newColCursor (rowCursorToNat newColCursor)

private
adjustColumnIndex : Nat -> Fin (S n)
adjustColumnIndex {n} prevColumn =
  case natToFin prevColumn (S n) of
       Nothing => last
       Just x => x

private
adjustColumnCursor : Nat -> RowCursor n
adjustColumnCursor {n = Z} _ = EmptyRowCursor
adjustColumnCursor {n = (S j)} k = RowCursor' $ adjustColumnIndex k

private
moveRowCursorByLine : Fin (S n) -> Move ByLine -> Fin (S n)
moveRowCursorByLine rowCursor (Backward k) =
  moveCursorBackward rowCursor k
moveRowCursorByLine rowCursor (Forward k) =
  moveCursorForward rowCursor k


moveByLine : Cursor v -> Move ByLine -> Cursor v
moveByLine (Cursor' rowCursor columnCursor prevColumn) movement =
  let newRowCursor = moveRowCursorByLine rowCursor movement
  in Cursor' newRowCursor (adjustColumnCursor prevColumn) prevColumn


