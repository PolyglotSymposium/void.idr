module Movement

%default total
%access public

data By =
  ByCharacter
  | ByLine

data Move : By -> Type where
  Backward : {by : By} -> Nat -> Move by
  Forward : {by : By} -> Nat -> Move by

%name Move movement

h : Nat -> Move ByCharacter
h x = Backward x

j : Nat -> Move ByLine
j x = Forward x

l : Nat -> Move ByCharacter
l x = Forward x

k : Nat -> Move ByLine
k x = Backward x

