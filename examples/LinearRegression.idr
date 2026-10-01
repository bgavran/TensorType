module LinearRegression

import Data.Tensor
import Data.Autodiff
import NN.Architectures
import NN.Optimisers
import NN.Training

||| The function we will be learning
groundTruthFn : Double -> Double
groundTruthFn x = 2 * x + 1

trainInputs : Tensor ["trainDatasetSize" ~~> 5] Double
trainInputs = ># [1, 2, 3, 4, 5]

trainDataset : Monad m => m (Dataset Double Double)
trainDataset = makeDataLoader trainInputs (pure . groundTruthFn)

testInputs : Tensor ["testDatasetSize" ~~> 4] Double
testInputs = ># [-100, 20, 50, 100]

testDataset : Monad m => m (Dataset Double Double)
testDataset = makeDataLoader testInputs (pure . groundTruthFn)

||| Runs a simple linear regression model
||| Run with `:exec linearRegression scalarAffine 1000 0.01` in the REPL
public export
linearRegression : (m : Const Double -\-> Const Double) ->
  Neg m.Params => FromDouble m.Params => ScientificDisplay m.Params =>
  Materialise m.Params =>
  (numSteps : Nat) ->
  (learningRate : Double) ->
  {default 1000 printEvery : Nat} ->
  IO Double
linearRegression m numSteps learningRate = do
  putStrLn "Training a linear regression model..."
  trainData <- trainDataset
  testData <- testDataset
  (pTrained, optState) <- train {printEvery}
    m
    SquaredError
    trainData
    (GDMomentum {mon=pMon m} {lr = fromDouble learningRate})
    numSteps
  -- Print predictions of a trained model on test data
  evalPrint m pTrained testInputs
  let avgLoss = averageLoss m SquaredError pTrained testData
  putStrLn "Average loss on the test dataset: \n  \{bold $ showSci avgLoss}"
  pure avgLoss