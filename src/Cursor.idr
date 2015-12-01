module Cursor

import Data.Fin
import Data.Vect

import Movement

%default total
%access public

private
data ColumnCursor : Nat -> Type where
  EmptyCursor : ColumnCursor Z
  ColumnCursor' : Fin (S k) -> ColumnCursor (S k)

private
zeroColumnCursor' : (n : Nat) -> ColumnCursor n
zeroColumnCursor' Z = EmptyCursor
zeroColumnCursor' (S k) = ColumnCursor' FZ

private
rowCursorToNat : ColumnCursor n -> Nat
rowCursorToNat EmptyCursor = Z
rowCursorToNat (ColumnCursor' x) = finToNat x

private
rowCursorToMaybeFin : ColumnCursor n -> Maybe (Fin n)
rowCursorToMaybeFin EmptyCursor = Nothing
rowCursorToMaybeFin (ColumnCursor' x) = Just x

abstract
data Cursor : Vect (S lastRow) Nat -> Type where
  Cursor' : {size : Vect (S lastRow) Nat} ->
            (rowCursor : Fin (S lastRow)) ->
            (colCursor : ColumnCursor (index rowCursor size)) ->
            (prevColumn : Nat) ->
            Cursor size

emptyBufferCursor : Cursor [Z]
emptyBufferCursor = Cursor' FZ EmptyCursor Z

zeroColumnCursor : Cursor size
zeroColumnCursor {size} = Cursor' FZ (zeroColumnCursor' $ index FZ size) Z

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
moveByCharInLine : ColumnCursor n -> Move ByCharacter -> ColumnCursor n 
moveByCharInLine EmptyCursor y = EmptyCursor
moveByCharInLine (ColumnCursor' x) (Backward k) = ColumnCursor' $ moveCursorBackward x k
moveByCharInLine (ColumnCursor' x) (Forward k) = ColumnCursor' $ moveCursorForward x k

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
adjustColumnCursor : Nat -> ColumnCursor n
adjustColumnCursor {n = Z} _ = EmptyCursor
adjustColumnCursor {n = (S j)} k = ColumnCursor' $ adjustColumnIndex k

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

tighten : Fin (S (S n)) -> Fin (S n)
tighten x =
  case (strengthen x) of
       Left _ => last
       Right x' => x'

deleteLine : {size : Vect (S (S k)) Nat} ->
            (cursor : Cursor size) ->
             Cursor (deleteAt (currentRowIndex cursor) size)
deleteLine (Cursor' rowCursor columnCursor prevColumn) =
  Cursor' (tighten rowCursor) (adjustColumnCursor prevColumn) prevColumn

