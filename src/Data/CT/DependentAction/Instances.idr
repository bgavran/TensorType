module Data.CT.DependentAction.Instances

import Data.CT.Category.Definition
import Data.CT.Category.Instances
import Data.CT.Functor.Definition
import Data.CT.Functor.Instances
import Data.CT.DependentAction.Definition

import Data.Container.Base
import Data.Container.Additive

namespace Type
  public export
  PairType : DepAct TypeCat (Const {c=TypeCat})
  PairType = MkDepAct $ \x => MkFunctor
    (x,)
    (\r, (x, p) => (x, r p))
  
  
  ||| X, X':X -> Set, DPair X X'
  public export
  DPairType : DepAct TypeCat (FamIndCat {c=TypeCat})
  DPairType = MkDepAct $ \x => MkFunctor
    (DPair x)
    (\r, (x ** p) => (x ** r x p))

namespace Cont
  public export
  PairCont : DepAct DLens (Const {c=DLens})
  PairCont = MkDepAct $ \c => MkFunctor
    (c ><)
    (hancockMap id)

  public export
  DPairCont : DepAct DLens (FamDLens {c=DLens})
  DPairCont = MkDepAct $ \c => MkFunctor
    (DepHancockProduct c)
    (\r => !% \(x ** p) => ((x ** (r x).fwd p) **
              \(x', p') => (x', (r x).bwd p p')))


namespace AddCont
  public export
  PairAddCont : DepAct AddDLens (Const {c=AddDLens})
  PairAddCont = MkDepAct $ \c => MkFunctor
    (c ><)
    (id ><)

  public export
  DPairAddCont : DepAct AddDLens (FamAddDLens {c=AddDLens})
  DPairAddCont = MkDepAct $ \c => MkFunctor
    (DepHancockProduct c)
    (\r => !%+ \(x ** p) => ((x ** (r x).fwd p) **
               \(x', p') => (x', (r x).bwd p p')))