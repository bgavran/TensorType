module Data.Container.Additive.Extension.Definition

import Data.Container.Base
import Data.Container.Additive.Object.Definition

public export
Path : AddCont -> Type
Path c = (x : c.Shp ** c.Pos x)