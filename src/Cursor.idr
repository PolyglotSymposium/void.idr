module Cursor

import Data.Fin

import Movement

%default total
%access public

record Cursor (bottomRow : Nat) where
  constructor Cursor'
  rowIndex : Fin (S bottomRow)
  colIndex : Nat

%name Cursor cursor

zeroCursor : Cursor n
zeroCursor = Cursor' FZ Z

updateColIndex : (Nat -> Nat) -> Cursor n -> Cursor n
updateColIndex update cursor = record { colIndex = update $ colIndex cursor } cursor

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
  -- TODO need proofs of the correctness of this logic
  if colIndex < S k
  then
    if colIndex + move < S k
    then colIndex + move
    else S k
  else colIndex

moving_within_empty_line_is_idempotent : moveByCharInLine move Z colIndex = colIndex
moving_within_empty_line_is_idempotent = Refl

-- TODO further proofs here once I understand how

moveByChar : Move ByCharacter -> Nat -> Cursor n -> Cursor n
moveByChar movement lineLength =
  updateColIndex $ moveByCharInLine movement lineLength

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

private
moveRowCursorByLine : Fin (S n) -> Move ByLine -> Fin (S n)
moveRowCursorByLine rowCursor (Backward k) =
  boundedSubtract rowCursor k
moveRowCursorByLine rowCursor (Forward k) =
  boundedAdd rowCursor k

moveByLine : Cursor v -> Move ByLine -> Cursor v
moveByLine (Cursor' rowCursor colIndex) movement =
  let newRowCursor = moveRowCursorByLine rowCursor movement
  in Cursor' newRowCursor colIndex

crimp : Fin (S (S n)) -> Fin (S n)
crimp x =
  case (strengthen x) of
       Left _ => last
       Right x' => x'

deleteLine : Cursor (S n) -> Cursor n
deleteLine (Cursor' rowCursor colIndex) =
  Cursor' (crimp rowCursor) colIndex

insertLineAbove : Cursor n -> Cursor (S n)
insertLineAbove {n} (Cursor' rowCursor colIndex) =
  Cursor' (weaken rowCursor) colIndex

