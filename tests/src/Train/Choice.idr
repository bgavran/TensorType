module Train.Choice

import Hedgehog

import System.Random
import Data.Vect
import Data.Fin
import Data.Tensor
import Data.Container.Additive
import Data.Autodiff
import NN.Architectures.LossFunctions

-- generic tests for choosing between branches


affineM : Const Double -\-> Const Double
affineM = withInit scalarAffine (pure (0.5, 0.0))

Branches : Vect 2 AddCont
Branches = [Const Double, Const Double]

branch : (i : Fin 2) -> Const Double -\-> index i Branches
branch 0 = affineM
branch 1 = affineM

contents : Const Double -\-> Section (\i => index i Branches)
contents = fanOutModel branch

||| Parameters of both branches, as `fanOutModel` lays them out
Params : Type
Params = ((Double, Double), ((Double, Double), ()))

params : Params
params = ((2.0, 1.0), ((3.0, 0.0), ()))

sec : (i : Fin 2) -> (index i Branches).Shp
sec 0 = the Double 1.0
sec 1 = the Double 3.0

losses : (i : Fin 2) -> Loss (index i Branches) (Const Double)
losses 0 = SquaredError
losses 1 = SquaredError

contentLoss : Loss (Section (\i => index i Branches)) (Const Double)
contentLoss = chosenBranchLoss {branches = fromVect Branches} losses

generators : Bag (i : Fin 2 ** (index i Branches).PosSet (sec i)) -> List (Nat, Double)
generators (MkBag gs) = map (\(i ** g) => (finToNat i, value i g)) gs
  where value : (i : Fin 2) -> (index i Branches).PosSet (sec i) -> Double
        value 0 g = g
        value 1 g = g

export
choiceGroup : Group
choiceGroup = MkGroup "Choice: sections and branch losses"
  [ ("fan-out forward is a function of the index", property1 $
      do the Double ((contents.fwd 3.0 params) 0) === 7.0
         the Double ((contents.fwd 3.0 params) 1) === 9.0)
  , ("fan-out backward places one generator at its branch", property1 $
      the (Double, Params) (contents.bwd 3.0 params (MkBag [(0 ** 1.0)]))
        === (2.0, ((3.0, 1.0), ((0.0, 0.0), ()))))
  , ("fan-out backward sums a bag over branches", property1 $
      the (Double, Params) (contents.bwd 3.0 params (MkBag [(0 ** 1.0), (1 ** 1.0)]))
        === (5.0, ((3.0, 1.0), ((3.0, 1.0), ()))))
  , ("branch loss compares in the label's fibre", property1 $
      the Double (contentLoss.Run.fwd (sec, (1 ** the Double 5.0))) === 4.0)
  , ("branch loss backward is the singleton bag at the label's index", property1 $
      let (bag, y') = contentLoss.Run.bwd (sec, (1 ** the Double 5.0)) 1.0
      in do generators bag === [(1, -4.0)]
            the Double y' === 4.0)
  ]
