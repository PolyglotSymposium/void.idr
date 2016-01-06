module Cursor

import Data.Fin

import Movement

%default total
%access public

private
crimp : Fin (S (S n)) -> Fin (S n)
crimp x =
  case (strengthen x) of
       Left _ => last
       Right x' => x'

private
boundedSubtract : Fin (S k) -> Nat -> Fin (S k)
boundedSubtract FZ _ = FZ
boundedSubtract (FS x) Z = (FS x)
boundedSubtract (FS x) (S k) = boundedSubtract (weaken x) k

private
boundedAdd : Fin (S k) -> Nat -> Fin (S k)
boundedAdd x Z = x
boundedAdd x (S k) =
  case strengthen x of
       Left _ => x
       Right x' => boundedAdd (FS x') k

record Cursor (bottomRow : Nat) where
  constructor Cursor'
  rowIndex : Fin (S bottomRow)
  colIndex : Nat

%name Cursor cursor

zeroCursor : Cursor n
zeroCursor = Cursor' FZ Z

private
updateColIndex : (Nat -> Nat) -> Cursor n -> Cursor n
updateColIndex update cursor = record { colIndex = update $ colIndex cursor } cursor

private
updateRowIndex : (Fin (S n) -> Fin (S m)) -> Cursor n -> Cursor m
updateRowIndex update (Cursor' rowIndex colIndex) = Cursor' (update rowIndex) colIndex

private
natToNullableFin : Nat -> Maybe (Fin n)
natToNullableFin {n = Z} _ = Nothing
natToNullableFin {n = (S _)} k = Just $ fromMaybe last $ natToFin k _

columnCursor : Cursor _ -> Maybe (Fin n)
columnCursor (Cursor' _ colIndex) = natToNullableFin colIndex

private
moveByCharInLine : Move ByCharacter -> Nat -> Nat -> Nat
moveByCharInLine movement Z colIndex = colIndex
moveByCharInLine (Backward move) (S k) colIndex = minus colIndex move
moveByCharInLine (Forward move) (S k) colIndex =
  case natToFin colIndex (S k) of
       Nothing => colIndex
       Just fin => finToNat $ boundedAdd fin move

moving_within_empty_line_is_idempotent : moveByCharInLine move Z colIndex = colIndex
moving_within_empty_line_is_idempotent = Refl

-- TODO further proofs here once I understand how

moveByChar : Move ByCharacter -> Nat -> Cursor n -> Cursor n
moveByChar movement lineLength =
  updateColIndex $ moveByCharInLine movement lineLength

private
moveRowCursorByLine : Move ByLine -> Fin (S n) -> Fin (S n)
moveRowCursorByLine (Backward k) rowCursor =
  boundedSubtract rowCursor k
moveRowCursorByLine (Forward k) rowCursor =
  boundedAdd rowCursor k

moveByLine : Move ByLine -> Cursor v -> Cursor v
moveByLine movement =
  updateRowIndex $ moveRowCursorByLine movement

deleteLine : Cursor (S n) -> Cursor n
deleteLine = updateRowIndex crimp

insertLineAbove : Cursor n -> Cursor (S n)
insertLineAbove = updateRowIndex weaken

-- TODO should actually truncate to end of line here
insertAfter : Nat -> Cursor n -> Cursor n
insertAfter n = updateColIndex (+ n)

-- TODO should actually behave differently than insertAfter
insertBefore : Nat -> Cursor n -> Cursor n
insertBefore k = updateColIndex (+ n)

