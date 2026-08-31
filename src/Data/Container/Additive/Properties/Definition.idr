module Data.Container.Additive.Properties.Definition

import Data.Container.Base
import Data.Container.Additive.Object.Definition

||| Convenience datatype storing the property that
||| an additive container `c` has an interface `i` on its positions
public export
InterfaceOnPositions : (c : AddCont) -> (i : Type -> Type) -> Type
InterfaceOnPositions c = InterfaceOnPositions (UC c)