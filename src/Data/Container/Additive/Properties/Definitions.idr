module Data.Container.Additive.Properties.Definitions

import Data.Container.Base
import Data.Container.Additive.Object.Definition

import Data.ComMonoid

||| Convenience datatype storing the property that
||| an additive container `c` has an interface `i` on its positions
public export
InterfaceOnPositions : (c : AddCont) -> (i : Type -> Type) -> Type
InterfaceOnPositions c = InterfaceOnPositions (UC c)



namespace Const
  public export
  data IsConst : AddCont -> Type where
    MkIsConst : (p : Type) -> (mon : ComMonoid p) => IsConst (MkAddCont (Const p))