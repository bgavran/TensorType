module Main

import Hedgehog
import Display2D.Instances
import Display2D.Expected
import Interfaces.Interfaces

public export
main : IO ()
main = test
  [ interfaceTests
    
  , cubicalTensorGroup
  , longTensorsGroup
  , cubicalTensorsDecimalGroup
  , treeTensorsGroup
  , listTensorsGroup ]