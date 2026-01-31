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
  Run : c.Hom ((depAct.act a).mapObj Param) b

public export
DepParaCat : {c : Cat} -> {m : IndCat c} ->
  (depAct : DepAct c m) ->
  Cat
DepParaCat depAct = MkCat c.Obj (DepParaMor depAct)

