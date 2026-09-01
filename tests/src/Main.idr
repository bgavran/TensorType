module Main

import Hedgehog

import Tensor.Interfaces
import Tensor.Indexing
import Tensor.Axis
import Tensor.Softargmax
import Display2D.Instances
import Display2D.Expected
import Train.LinearRegression
import Train.Optimisers
import Train.Model
import Train.TensorPrimitives
import Sampling

public export
main : IO ()
main = do
  -- the Hedgehog port has no evalIO, so groups that train are run here
  trainGr <- trainGroup
  test
    [ cubicalIndexingGroup
    , indexingGroup

    , interfaceTests
    , axisTests
    , softargmaxGroup
    , optimisersGroup
    , samplingGroup

    -- printing stuff
    , cubicalTensorGroup
    , longTensorsGroup
    , cubicalTensorsDecimalGroup
    , treeTensorsGroup
    , listTensorsGroup

    , modelGroup
    , tensorPrimitivesGroup
    , trainGr ]
