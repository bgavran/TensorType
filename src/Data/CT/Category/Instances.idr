module Data.CT.Category.Instances

import Data.CT.Category.Definition
import Data.CT.Functor.Definition

import Data.Container.Base
import Data.Container.Additive

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

||| Category of additive dependent lenses
public export
AddDLens : Cat
AddDLens = MkCat AddCont (=%>)

||| Category of additive dependent charts
public export
AddDChart : Cat
AddDChart = MkCat AddCont (=&>)
