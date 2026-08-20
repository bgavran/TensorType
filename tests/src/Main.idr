module Main

import Hedgehog

import Tensor.Interfaces
import Tensor.Indexing
import Tensor.Axis
import Tensor.Softargmax
import Tensor.Contractions
import Display2D.Instances
import Display2D.Expected
import Train.LinearRegression
import Train.Optimisers
import Sampling

public export
main : IO ()
main = do
  trainGr <- trainGroup -- kind of a hack, as Hedgehog does not have evalIO
  test
    [ cubicalIndexingGroup
    , indexingGroup

    , interfaceTests
    , axisTests
    , softargmaxGroup
    , contractionsGroup
    , optimisersGroup
    , samplingGroup
      
    , cubicalTensorGroup
    , longTensorsGroup
    , cubicalTensorsDecimalGroup
    , treeTensorsGroup
    , listTensorsGroup
    
    , trainGr ]