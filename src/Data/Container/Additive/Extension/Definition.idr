module Data.Container.Additive.Extension.Definition

import Data.Container.Base
import Data.Container.Additive.Object.Definition
import Data.Container.Additive.Morphism.Definition
import Data.ComMonoid

||| A functor `AddCont -> [ComMon, Type]`
public export
record Ext (0 c : AddCont) (y : ComMonoid) where
  constructor (<|)
  shapeExt : c.Shp
  index : ComMonoidHomo (UMon c shapeExt) y


||| Analogous to one in `Base.Extension.Definition`
public export
extMap : {0 y : ComMonoid} -> {0 c, d : AddCont} ->
  c =%+> d -> Ext c y -> Ext d y
extMap f (sh <| index) = let (y ** ky) = (%!+) f sh
                         in y <| (index . ky)