module Data.Container.Additive.Extension.Definition

import Data.Container.Base
import Data.Container.Additive.Object.Definition

||| If extension of a container is a functor Type -> Type, what is an extension
||| of an additive container?
public export
Ext : AddCont -> Type -> Type
Ext c x = Ext (UC c) x