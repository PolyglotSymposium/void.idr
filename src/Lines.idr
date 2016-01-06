module Lines

import Data.Fin
import Data.Vect

import SizedStrings

%default total
%access public

data Lines : Vect k Nat -> Type where
  Nil : Lines []
  (::) : SizedString n -> Lines v -> Lines (n :: v)

%name Lines linez -- so as to avoid confusion with lines function

index : {v : Vect k Nat} -> (i : Fin k) -> Lines v -> SizedString (index i v)
index FZ (x :: xs) = x
index (FS y) (x :: xs) = index y xs

replaceAt : { size : Vect (S k) Nat } ->
           (i : Fin (S k)) ->
           SizedString (index i size) -> 
           Lines size ->
           Lines size
replaceAt FZ     str (x::xs) = str :: xs
replaceAt (FS i) str (x::[]) = absurd i
replaceAt (FS i) str (x::(y :: z)) = x :: replaceAt i str (y :: z)

replaceAndResizeAt : { size : Vect (S k) Nat } ->
                     (i : Fin (S k)) ->
                     SizedString n -> 
                     Lines size ->
                     Lines (replaceAt i n size)
replaceAndResizeAt FZ     str (x::xs) = str :: xs
replaceAndResizeAt (FS i) str (x::[]) = absurd i
replaceAndResizeAt (FS i) str (x::(y :: z)) = x :: replaceAndResizeAt i str (y :: z)

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

deleteLine : {v : Vect (S k) Nat} -> (i : Fin (S k)) -> Lines v -> Lines (deleteAt i v)
deleteLine FZ (str :: strs) = strs
deleteLine {k = Z} (FS i) _ = absurd i
deleteLine {k = S j} (FS i) (str :: strs) = str :: deleteLine i strs

insertLine : {v : Vect k Nat} -> (i : Fin (S k)) -> (s: SizedString n) -> Lines v ->
             Lines (insertAt i n v)
insertLine FZ s ls = s :: ls
insertLine (FS y) s [] = absurd y
insertLine (FS y) s (str :: ls) = str :: insertLine y s ls

replaceChar : {size : Vect (S k) Nat} ->
              (row : Fin (S k)) ->
              (column : Maybe (Fin (index row size))) ->
              Char ->
              Lines size ->
              Lines size
replaceChar row Nothing c linez = linez
replaceChar row (Just i) c linez =
  replaceAt row (replaceAt' i $ index row linez) linez where
    replaceAt' : Fin n -> SizedString n -> SizedString n
    replaceAt' {n = Z} i _ = absurd i
    replaceAt' {n = (S k)} i str = replaceAt i c str

InsertAfterType : (size : Vect (S k) Nat) ->
                  (row : Fin (S k)) ->
                  Nat ->
                  Type
InsertAfterType size row textLength =
  Lines $ replaceAt row (index row size + textLength) size

insertAfter : {size : Vect (S k) Nat} ->
             (row : Fin (S k)) ->
             (column : Maybe (Fin (index row size))) ->
             SizedString l ->
             Lines size ->
             InsertAfterType size row l
insertAfter row column str linez =
  replaceAndResizeAt row (insertAfter (index row linez) column str) linez

