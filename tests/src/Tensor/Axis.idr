module Tensor.Axis

import Hedgehog
import Data.Tensor

BatchSize : Axis
BatchSize =  "batchSize" ~> Vect 32
  
SeqLen : Axis
SeqLen = "seqLen" ~> List
  
FeatureSize : Axis
FeatureSize = "featureSize" ~> Vect 128
  
BatchSizeNew : Axis
BatchSizeNew = "batchSize" ~> Vect 13
  
testBinding0 : Tensor [] Double
  
testBinding1 : Tensor [SeqLen] Double
  
testBinding12 : Tensor [SeqLen, SeqLen] Double
  
testBinding2 : Tensor [BatchSize, SeqLen] Double
  
testBinding3 : Tensor [BatchSize, SeqLen, FeatureSize] Double
  
testBinding4 : Tensor [BatchSize, SeqLen, FeatureSize, FeatureSize] Double
  
failing
  ||| This fails because the same name here refers to two different sizes
  failBinding1 : Tensor [BatchSize, BatchSizeNew] Double
  
  ||| Same here 
  failBinding2 : Tensor [BatchSize, rename SeqLen "batchSize"] Double


||| This test should trivially pass if everything above it compiles
export
axisTests : Group
axisTests = MkGroup "Axis tests"
  [ ("Axis tests", property1 success) ]