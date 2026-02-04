module NN.Training.Optimisation

import Data.Tensor
import Data.Container.Additive
import NN.Optimisers.Definition
import NN.Optimisers.Instances
import NN.Utils
import Data.Para

{-------------------------------------------------------------------------------
{-------------------------------------------------------------------------------
This file defines functions which perform pure optimisation:
optimisation of a differentiable function `f : p -> x` (here modelled as a lens `f : p =%> x` via some optimiser such as gradient descent. 
Here no "loss function" or "input-output pairs" are needed, just a function to optimise.

This file provides functionality for creating, and turning supervised learning problems into pure optimisation problems, via a function which takes:
a) a parametric lens `f : x >< p =%>> y`
b) a loss function `loss : (y, y) =%> l`
c) input-output pairs `IO (x.Shp, y.Shp)`
and composes them to produce an optimisation problem `f : p =%> l` which the above described functions can consume.

Notably, only a *non-dependent* supervised-learning problem can be turned into a pure optimisation one. If the parameter space depends on the input, then learning becomes its own thing.

-------------------------------------------------------------------------------}
-------------------------------------------------------------------------------}

||| Functions which performs a single set of optimisation of a function
||| `f : p -> x` via some (possibly stateful) optimiser . Both are here
||| treated as dependent lenses.
public export
optimiseStep : {p, x : AddCont} -> InterfaceOnPositions x Num =>
  (fIO : IO (p =%> x)) ->
  (optimiser : Optimiser p stateTy) ->
  (p.Shp, stateTy) -> IO (p.Shp, stateTy) -- parameter update function
optimiseStep fIO (MkOptimiser opt _ _) (p, state)= do
   f <- fIO
   pure $ fromCostate (opt %>> ULens (f %>> constantOne {c=x})) (p, state)

||| Performs function optimisation for `numSteps : Nat` times, while logging 
||| the progress to the console.
public export
optimise : {p, x : AddCont} -> InterfaceOnPositions x Num =>
  Show p.Shp => Show x.Shp => Show stateTy =>
  (fIO : IO (p =%> x)) ->
  (opt : Optimiser p stateTy) ->
  (numSteps : Nat) ->
  IO (p.Shp, stateTy)
optimise fIO opt numSteps = do
  currentValue <- opt.initParam
  currentState <- opt.initState
  runActionUntilMaxSteps (optimiseStep fIO opt) numSteps 0 (currentValue, currentState) (do loss <- fIO ; pure $ loss.fwd . opt.fwd)

||| Given
||| a) a parametric lens `f : x >< p =%> y`
||| b) a loss function `loss : y >< y =%> l`
||| c) dataSampler `IO (x.Shp, y.Shp)`
||| builds a IO optimisation problem `IO (p =%> l)`
public export
buildSupervisedLearningSystem : {p, x, y, l : AddCont} ->
  (f : (x >< p) =%> y) ->
  (loss : (y >< y) =%> l) ->
  (dataSampler : IO (x.Shp, y.Shp)) ->
  Show x.Shp => Show y.Shp =>
  IO (p =%> l) -- the inputs here are what's changing at each iteration
buildSupervisedLearningSystem f loss dataSampler = do
  (x, yTrue) <- dataSampler
  -- putStrLn "Processing input-output pair: \{show x}, \{show yTrue}"
  let withLoss = (f >< id) %>> loss
      withInputs = ((State x >< id) >< State yTrue) %>> withLoss
  pure $ leftUnitInv %>> rightUnitInv %>> withInputs

public export
optimiseLearner : {x, y, l : AddCont} -> InterfaceOnPositions l Num =>
  (f : ParaAddDLens x y) ->
  Show (GetParam f).Shp =>
  Show x.Shp => Show y.Shp => Show stateTy => Show l.Shp =>
  (loss : (y >< y) =%> l) ->
  (dataSampler : IO (x.Shp, y.Shp)) ->
  (opt : Optimiser (GetParam f) stateTy) ->
  (numSteps : Nat) ->
  IO ((GetParam f).Shp, stateTy)
optimiseLearner (MkPara p f) loss dataSampler
  = optimise (buildSupervisedLearningSystem f loss dataSampler)