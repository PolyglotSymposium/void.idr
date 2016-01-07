module MaybeFin

import Data.Fin

%default total
%access public

data MaybeFin : Nat -> Type where
  NoFin : MaybeFin Z
  SomeFin : Fin (S k) -> MaybeFin (S k)

instance Cast (MaybeFin n) (Maybe (Fin n)) where
  cast NoFin = Nothing
  cast (SomeFin x) = Just x
