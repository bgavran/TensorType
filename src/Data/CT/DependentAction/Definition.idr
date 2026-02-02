module Data.CT.DependentAction.Definition

import Data.CT.Category.Definition
import Data.CT.Category.Instances
import Data.CT.Functor.Definition
import Data.CT.Functor.Instances

public export
record DepAct (c : Cat) (i : IndCat c) where
  constructor MkDepAct
  Act : (x : c.Obj) -> Functor (i.mapObj x) c

