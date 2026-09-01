module Train.LinearRegression

import Hedgehog

import System.Random

import Data.Tensor
import Data.Container.Additive
import Data.Autodiff
import NN.Architectures
import NN.Training
import NN.Training.Examples.LinearRegression

export
trainGroup : IO Group
trainGroup = do
  loss <- linearRegression scalarAffine 10000
  pure $ MkGroup "Neural network training"
    [ ("Linear regression", property1 $ diff loss (<) 0.0001) ]
