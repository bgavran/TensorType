module NN.Training.Training

import Data.Tensor
import Data.Container.Additive
import NN.Optimisers.Definition
import NN.Optimisers.Instances
import NN.Utils
import Data.Para

{-------------------------------------------------------------------------------
{-------------------------------------------------------------------------------
todo will attempt to update this for monadic dependent lenses
This file defines functions which perform pure optimisation:
optimisation of a differentiable function `f : p -> x` (here modelled as a lens `f : p =%> x` via some optimiser such as gradient descent. 
Here no "loss function" or "input-output pairs" are needed, just a function to optimise.

This file provides functionality for creating, and turning supervised learning problems into pure optimisation problems, via a function which takes:
a) a parametric lens `f : x >< p =%>> y`
b) a loss function `loss : (y, y) =%> l`
c) input-output pairs `IO (x.Shp, y.Shp)`
and composes them to produce an optimisation problem `f : p =%> l` which the above described functions can consume.

Notably, only a *non-dependent* supervised-learning problem can be turned into a pure optimisation one. If the parameter space depends on the input, then learning becomes its own thing.


todo using Hom-version of optimisation becomes problematic if we either
a) have the dependency of the parameter on the input
b) use monadic lenses

-------------------------------------------------------------------------------}
-------------------------------------------------------------------------------}

||| Functions which performs a single set of optimisation of a function
||| `f : p -> x` via some (possibly stateful) optimiser . Both are here
||| treated as dependent lenses.
public export
optimiseStep : {p, x : AddCont} -> InterfaceOnPositions x Num =>
  (fIO : IO (MAddLens {m=IO} p x)) ->
  (optimiser : Optimiser p stateTy) ->
  (p.Shp, stateTy) -> IO (p.Shp, stateTy) -- parameter update function
optimiseStep fIO (MkOptimiser opt _ _) (p, state)= do
   f <- fIO
   fromCostate ((liftDLens opt) %%>> UMLens (f %%+>> liftAddDLens (constantOne {c=x}))) (p, state)

||| Performs function optimisation for `numSteps : Nat` times, while logging 
||| the progress to the console.
public export
optimise : {p, x : AddCont} -> InterfaceOnPositions x Num =>
  {default 100 printEvery : Nat} ->
  {default Nothing initParam : Maybe p.Shp} ->
  Show p.Shp => Show x.Shp => Show stateTy =>
  (fIO : IO (MAddLens {m=IO} p x)) ->
  (opt : Optimiser p stateTy) ->
  (numSteps : Nat) ->
  IO (p.Shp, stateTy)
optimise fIO opt numSteps = do
  currentValue <- case initParam of
    Just p => pure p
    Nothing => opt.initParam
  currentState <- opt.initState
  runActionUntilMaxSteps
    {l=x.Shp}
    {printEvery=printEvery}
    (optimiseStep fIO opt)
    numSteps 0
    (currentValue, currentState)
    (\pSt => do
      loss <- fIO
      loss.fwd (opt.fwd pSt))

||| todo we keep building the lens from scratch at every iteration
||| Given
||| a) a parametric lens `f : x >< p =%> y`
||| b) a loss function `loss : y >< y =%> l`
||| c) dataSampler `IO (x.Shp, y.Shp)`
||| builds a IO optimisation problem `IO (p =%> l)`
public export
buildSupervisedLearningSystem : {m : Type -> Type} -> Monad m =>
  {p, x, y, l : AddCont} ->
  (f : MAddLens {m} (x >< p) y) ->
  (loss : MAddLens {m} (y >< y) l) ->
  (dataSampler : IO (x.Shp, y.Shp)) ->
  Show x.Shp => Show y.Shp =>
  IO (MAddLens {m} p l)
buildSupervisedLearningSystem f loss dataSampler = do
  (x, yTrue) <- dataSampler
  let withLoss = (f >< id) %%+>> loss
      withInputs = ((State x >< id) >< State yTrue) %%+>> withLoss
  -- putStrLn "Processing input-output pair: \{show x}, \{show yTrue}"
  pure $ leftUnitInv %%+>> rightUnitInv %%+>> withInputs

public export
train : {x, y, l : AddCont} -> InterfaceOnPositions l Num =>
  {default 100 printEvery : Nat} ->
  (f : ParaAddMLens {m=IO} x y) ->
  Show (GetParam f).Shp =>
  Show x.Shp => Show y.Shp => Show stateTy => Show l.Shp =>
  {default Nothing initParam : Maybe (GetParam f).Shp} ->
  (loss : MAddLens {m=IO} (y >< y) l) ->
  (dataSampler : IO (x.Shp, y.Shp)) ->
  (opt : Optimiser (GetParam f) stateTy) ->
  (numSteps : Nat) ->
  IO ((GetParam f).Shp, stateTy)
train (MkPara p f) loss dataSampler = optimise
  {printEvery=printEvery}
  {initParam=initParam}
  (buildSupervisedLearningSystem f loss dataSampler)


public export
totalLoss : {x, y : AddCont} ->
  (f : ParaAddMLens {m=IO} x y) ->
  (loss : MAddLens {m=IO} (y >< y) l) ->
  (p : (GetParam f).Shp) ->
  Show l.Shp => Num l.Shp =>
  (testData : Vect n (x.Shp, y.Shp)) ->
  IO l.Shp
totalLoss (MkPara pCont f) loss p [] = pure 0
totalLoss (MkPara pCont f) loss p ((x, yTrue) :: xs) = do
  (yPred ** _) <- (%%!+) f (x, p)
  (lossVal ** _) <- (%%!+) loss (yPred, yTrue)
  lossRemaining <- totalLoss (MkPara pCont f) loss p xs
  pure (lossVal + lossRemaining)

public export
averageLoss : {x, y : AddCont} -> {n : Nat} ->
  (f : ParaAddMLens {m=IO} x y) ->
  (loss : MAddLens {m=IO} (y >< y) l) ->
  (p : (GetParam f).Shp) ->
  Show l.Shp => Num l.Shp => Fractional l.Shp =>
  Cast Nat l.Shp =>
  (testData : Vect n (x.Shp, y.Shp)) ->
  IO l.Shp
averageLoss f loss p testData = do
  totalLoss <- totalLoss f loss p testData
  pure (totalLoss / cast n)

public export
evalWithLoss : {x, y : AddCont} ->
  (f : ParaAddMLens {m=IO} x y) ->
  (loss : MAddLens {m=IO} (y >< y) l) ->
  (p : (GetParam f).Shp) ->
  Show x.Shp => Show y.Shp => Show l.Shp =>
  (testData : Vect n (x.Shp, y.Shp)) ->
  IO ()
evalWithLoss f loss p [] = pure ()
evalWithLoss (MkPara pCont f) loss p ((x, yTrue) :: xs) = do
  (yPred ** _) <- (%%!+) f (x, p)
  (lossVal ** _) <- (%%!+) loss (yPred, yTrue)
  putStrLn "Input: \{show x}, Predicted: \{show yPred}, Loss: \{show lossVal}"
  evalWithLoss (MkPara pCont f) loss p xs

public export
eval : {x, y : AddCont} ->
  (f : ParaAddMLens {m=IO} x y) ->
  (p : (GetParam f).Shp) ->
  Show x.Shp => Show y.Shp =>
  (testData : Vect n x.Shp) ->
  IO ()
eval _ _ [] = pure ()
eval (MkPara pCont f) p (x :: xs) = do
  (yPred ** _) <- (%%!+) f (x, p)
  putStrLn "Input: \{show x}, Predicted: \{show yPred}"
  eval (MkPara pCont f) p xs


public export
debugPrint : {x, y : AddCont} ->
  Show x.Shp => Show y.Shp =>
  (name : String) ->
  (f : ParaAddMLens {m=IO} x y) ->
  Show (GetParam f).Shp =>
  ParaAddMLens {m=IO} x y
debugPrint name (MkPara pCont f) = MkPara
  pCont
  (!%%+ \(x, p) => do
    putStrLn "--------------------------------"
    putStrLn "\{name} input: \{show x}"
    putStrLn "\{name} parameter: \{show p}"
    (y ** ky) <- (%%!+ f) (x, p)
    putStrLn "\{name} output: \{show y}"
    putStrLn "--------------------------------"
    pure (y ** ky))
