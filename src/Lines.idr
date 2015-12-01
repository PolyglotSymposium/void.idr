module Lines

import Data.Fin
import Data.Vect

import SizedStrings

%default total
%access public

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

