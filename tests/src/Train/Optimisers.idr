module Train.Optimisers

import Hedgehog

import Data.Tensor
import NN.Optimisers

momentumIsGDStep : (Double, Double)
momentumIsGDStep = momentumUpdate {lr=0.1} 0.0 5.0 3.0 2.0

adamFirstStep : (Double, Double, Double, Double, Double)
adamFirstStep = adamUpdate {lr=0.1} 0.9 0.999 1.0e-8 1.0 0 0 1 1 2.0

export
optimisersGroup : Group
optimisersGroup = MkGroup "Optimisers"
  [ ("Momentum with gamma=0 is a GD step", property1 $
      let (p', s') = momentumIsGDStep
      in do p' === 5.0 - 0.1 * 2.0
            s' === 2.0)
  , ("Adam's first step moves by ~lr against the gradient", property1 $
      let (p', m', v', b1p', b2p') = adamFirstStep
      in do assert (isClose p' (1.0 - 0.1))
            assert (isClose m' 0.2)
            assert (isClose v' 0.004)
            b1p' === 0.9
            b2p' === 0.999)
  ]
