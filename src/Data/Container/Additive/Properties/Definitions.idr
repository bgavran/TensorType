module Data.Container.Additive.Properties.Definitions

import Data.Container.Base
import Data.Container.Additive.Object.Definition

import Data.ComMonoid


||| Convenience datatype storing the property that
||| an additive container `c` has an interface `i` on its positions
public export
data InterfaceOnPositions : (c : AddCont) -> (i : Type -> Type) -> Type where
  ||| For every shape s the set of positions c.Pos s has that interface
  MkI : (p : (s : c.Shp) -> i (c.Pos s)) =>
    InterfaceOnPositions c i


namespace Flat
  public export
  data IsFlat : AddCont -> Type where
    MkIsFlat : (p : Type) -> (mon : ComMonoid p) => IsFlat (MkAddCont (Const p))

  --flatEq : IsFlat c => c = MkAddCont (Const c.Shp)