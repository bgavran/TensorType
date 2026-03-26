module Data.Container.Additive.Extension.Definition

import Data.Container.Base
import Data.Container.Additive.Object.Definition

public export
Ext : AddCont -> Type -> Type
Ext c x = Ext (UC c) x

||| Can be represented as a derivative
public export
Path : AddCont -> Type
Path c = (x : c.Shp ** c.Pos x)