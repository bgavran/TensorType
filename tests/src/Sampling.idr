module Sampling

import Hedgehog

import Data.Tensor
import Control.Monad.Distribution
import Control.Monad.Sample.Definition
import Control.Monad.Sample.Instances
import Control.Monad.Identity
import Data.Fin

export
samplingGroup : Group
samplingGroup = MkGroup "Sampling"
  [ ("Sampling a Dirac delta with pickMax returns the index", property1 $
      runIdentity (fromCostate (sample @{pickMax}) (diracDelta {a="test" ~~> 5} 2)) === 2)
  ]
