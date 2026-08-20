module NN.Training.Examples.LinearRegression

import System.Random

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
linearRegression : (f : ParaAddLens (Const Double) (Const Double)) ->
  Neg (GetParam f).Shp => Fractional (GetParam f).Shp =>
  Sqrt (GetParam f).Shp =>
  Random (GetParam f).Shp =>
  FromDouble (GetParam f).Shp => ScientificDisplay (GetParam f).Shp =>
  (isFlat : IsConst (GetParam f)) =>
  (numSteps : Nat) ->
  {default 1000 printEvery : Nat} ->
  IO Double
linearRegression f@(MkPara (MkAddCont (Const p)) _)
  {isFlat = MkIsConst p @{mon}} numSteps = do
  putStrLn "Training a linear regression model..."
  trainData <- linearRegressionDataLoader
  testDataLoader <- makeDataLoader [20, 50, 100] (pure . groundTruth)
  pTrained <- fst <$> optimise
    {printEvery=printEvery}
    {l=Const Double, e=SupervisedData Double Double}
    (buildSupervisedLearningSystem f SquaredDifference)
    (handleData trainData)
    (GDMomentum {pType=(GetParam f).Shp})
    numSteps
  fromCostate (eval f pTrained) (snd $ inputs testDataLoader)
  avgLoss <- fromCostate (averageLoss f SquaredDifference pTrained) (dataset testDataLoader)
  putStrLn "Average loss: \{showSci avgLoss}"
  pure avgLoss






{- 
public export
minimiseCopyMulGD : (startingValue : Double) ->
  (numSteps : Nat) ->
  IO Double
minimiseCopyMulGD startingValue numSteps =
  let opt = GD {pType=Double} {lr=0.001}
  in fst <$> optimise {e=Scalar} ?hehe opt numSteps

public export
minimiseCopyMulMomentum : (startingValue : Double) ->
  (numSteps : Nat) ->
  IO Double
minimiseCopyMulMomentum startingValue numSteps =
  let opt = GDMomentum {pType=Double} {lr=0.001} {gamma=0.9}
  in fst <$> optimise (pure $ (Copy %>> Mul)) opt numSteps

{-
public export
DotTensor : {n: Nat} ->
  (Tensor [n] Double, Tensor [n] Double) -> Tensor [] Double
DotTensor (t1, t2) = dot t1 t2

public export
dotDifferentiable : {n : Nat} -> BwDifferentiable (DotTensor {n})
dotDifferentiable = MkBwDiff (\(t1, t2), dt =>
  ((\x => x * extract dt) <$> t2, (\x => x * extract dt) <$> t1))


public export
assembleLearningSystem :
  Para Unit input ->
  Para input output ->
  Para output l ->
  Para Unit l
assembleLearningSystem pi pf pl = pi \>> pf \>> pl


public export
train : {input, output, l : Type} ->
  Show l =>
  (model : Model input output) ->
  (init : (x : input) -> IO (Param model x)) ->
  (dataSampler : IO (input, output)) ->
  (loss : (output, output) -> l) ->
  IO ()
train model init dataSampler loss = do
  (x, yTrue) <- dataSampler
  p <- init x
  let yPred = Run model x p
  let l' = loss (yPred, yTrue)
  print l'
  pure ?hmm