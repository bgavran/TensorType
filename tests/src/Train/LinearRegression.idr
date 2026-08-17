module Train.LinearRegression

import System.Random
import Hedgehog

import Data.Tensor
import Data.Autodiff
import NN.Architectures
import NN.Training
import NN.Training.Examples.LinearRegression

train1000StepsLinReg : IO Double
train1000StepsLinReg = linearRegression {printEvery=1000} AffineParametric 10000

-- Kind of a hack right, as the Hedgehog port does not have evalIO
public export
trainGroup : IO Group
trainGroup = do
  loss <- train1000StepsLinReg
  pure $ MkGroup "Neural network training"
    [ ("Linear regression", property1 $ diff loss (<) 0.0001) ]