module Data.Container.Additive.Extension.Definition

import Data.Container.Base
import Data.Container.Additive.Object.Definition
import Data.ComMonoid

||| A functor `AddCont -> [ComMon, Type]`
public export
record Ext (0 c : AddCont) (y : ComMonoid) where
  constructor (<|)
  shapeExt : c.Shp
  index : ComMonoidHomo (UMon c shapeExt) y
