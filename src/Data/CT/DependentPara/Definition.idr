module Data.CT.DependentPara.Definition

import Data.CT.Category.Definition
import Data.CT.Category.Instances
import Data.CT.Functor.Definition
import Data.CT.Functor.Instances
import Data.CT.DependentAction.Definition
import Data.CT.DependentAction.Instances

||| Data structure holding the morphisms of dependent para
public export
record DepParaMor
  {c : Cat}
  {m : IndCat c}
  (depAct : DepAct c m)
  (a, b : c.Obj)
  where
  constructor MkPara
  Param : (m.mapObj a).Obj
  Run : c.Hom ((depAct.Act a).mapObj Param) b

public export
DepParaCat : {c : Cat} -> {m : IndCat c} ->
  (depAct : DepAct c m) ->
  Cat
DepParaCat depAct = MkCat c.Obj (DepParaMor depAct)


||| We do not define composition or anything else here. This is because, if we
||| did, we'd have to define a lot of other things, like composition in the 
||| base category, and associators of the monoidal category and actegory
||| While the type below would be "simple", its full abstract implementation is 
||| not necessary for us
public export
composeParaNotUsed : {c : Cat} -> {m : IndCat c} ->
  {depAct : DepAct c m} ->
  {x, y, z : c.Obj} ->
  DepParaMor {c=c} {m=m} depAct x y ->
  DepParaMor {c=c} {m=m} depAct y z ->
  DepParaMor {c=c} {m=m} depAct x z