module Data.CT.Category.Instances

import Data.CT.Category.Definition
import Data.CT.Functor.Definition

import Data.Container.Base

public export
TypeCat : Cat
TypeCat = MkCat Type (\a, b => a -> b)

public export
Cat : Cat
Cat = MkCat Cat Functor

public export
opCat : Cat -> Cat
opCat c = MkCat c.Obj (flip c.Hom)

public export
DLens : Cat
DLens = MkCat Cont (=%>)

public export
DChart : Cat
DChart = MkCat Cont (=&>)
