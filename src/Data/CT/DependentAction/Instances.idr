module Data.CT.DependentAction.Instances

import Data.CT.Category.Definition
import Data.CT.Category.Instances
import Data.CT.Functor.Definition
import Data.CT.Functor.Instances
import Data.CT.DependentAction.Definition

import Data.Container.Base
import Data.Container.Additive

||| X, X':X -> Set, DPair X X'
public export
DepActOnType : DepAct TypeCat (FamIndCat {c=TypeCat})
DepActOnType = MkDepAct $ \x => MkFunctor
  (DPair x)
  (\r, (x ** p) => (x ** r x p))

public export
DepActOnCont : DepAct DLens (FamDLens {c=DLens})
DepActOnCont = MkDepAct $ \c => MkFunctor
  (\pCont => ((x ** p) : DPair c.Shp (Shp . pCont)) !>
             (c.Pos x, (pCont x).Pos p))
  (\r => !% \(x ** p) => ((x ** (r x).fwd p) **
            \(x', p') => (x', (r x).bwd p p')))


public export
DepActOnAddCont : DepAct AddDLens (FamAddDLens {c=AddDLens})
DepActOnAddCont = MkDepAct $ \c => MkFunctor
  (DepHancockProduct c)
  (\r => !%+ \(x ** p) => ((x ** (r x).fwd p) **
             \(x', p') => (x', (r x).bwd p p')))