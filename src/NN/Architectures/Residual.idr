module NN.Architectures.Residual

import Data.Para

public export
addResidual : Num a => a -\-> a -> a -\-> a
addResidual (MkPara param f) = MkPara param
  $ \(input ** p) => f (input ** p) + input
