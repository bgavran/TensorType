module NN.Training.Examples.LinearRegression

import Data.Tensor
import Data.Autodiff
import NN.Architectures
import NN.Optimisers
import NN.Training

public export
exampleInputs : Vect 5 Double
exampleInputs = [1, 2, 3, 4, 5]

public export
groundTruth : Double -> Double
groundTruth x = 2 * x + 1

public export
linearRegressionDataLoader : Monad m => m (DataLoader Double Double)
linearRegressionDataLoader = makeDataLoader exampleInputs (pure . groundTruth)

public export
linearRegression : (m : Const Double -\-> Const Double) ->
  Neg m.Params => FromDouble m.Params => ScientificDisplay m.Params =>
  Materialise m.Params =>
  (numSteps : Nat) ->
  {default 1000 printEvery : Nat} ->
  IO Double
linearRegression m@(MkModel p @{mon} _ _) numSteps = do
  putStrLn "Training a linear regression model..."
  trainData <- linearRegressionDataLoader
  testDataLoader <- makeDataLoader [20, 50, 100] (pure . groundTruth)
  pTrained <- fst <$> train {printEvery}
    m
    SquaredError
    trainData
    GDMomentum
    numSteps
  evalPrint m pTrained testDataLoader
  let avgLoss = Model.averageLoss m SquaredError pTrained testDataLoader
  putStrLn "Average loss: \{showSci avgLoss}"
  pure avgLoss