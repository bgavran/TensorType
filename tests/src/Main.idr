module Main

import Hedgehog

import Tensor.Interfaces
import Tensor.Indexing
import Display2D.Instances
import Display2D.Expected

public export
main : IO ()
main = test
  [ cubicalIndexingGroup

  , interfaceTests
    
  , cubicalTensorGroup
  , longTensorsGroup
  , cubicalTensorsDecimalGroup
  , treeTensorsGroup
  , listTensorsGroup ]