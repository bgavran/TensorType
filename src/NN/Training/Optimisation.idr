module NN.Training.Optimisation

import Data.Tensor
import Data.Container.Additive
import NN.Optimisers.Definition
import NN.Optimisers.Instances
import NN.Training.Utils
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
  (f : p =%> x) ->
  (optimiser : Optimiser p stateTy) ->
  (p.Shp, stateTy) -> (p.Shp, stateTy) -- parameter update function
optimiseStep f (MkOptimiser opt) = fromCostate $ 
  opt %>> ULens (f %>> constantOne {c=x})

||| Performs function optimisation for `numSteps : Nat` times, while logging 
||| the progress to the console.
public export
optimise : {p, x : AddCont} -> InterfaceOnPositions x Num =>
  Show p.Shp => Show stateTy =>
  (f : p =%> x) ->
  (opt : Optimiser p stateTy) ->
  (currentValue : p.Shp) -> (currentState : stateTy) ->
  (numSteps : Nat) ->
  IO (p.Shp, stateTy)
optimise f opt currentValue currentState numSteps = runActionUntilMaxSteps
  (\(currVal, currState) => pure $ optimiseStep f opt (currVal, currState))
  numSteps
  0
  (currentValue, currentState)

||| Given
||| a) a parametric lens `f : x >< p =%> y`
||| b) a loss function `loss : y >< y =%> l`
||| c) and an input-output pair `IO (x.Shp, y.Shp)`
||| builds an optimisation problem `f : p =%> l`
public export
buildSupervisedLearningSystem : {p, x, y, l : AddCont} ->
  (f : p =%> InternalLensAdditive x y) ->
  (loss : (y >< y) =%> l) ->
  (ioPair : (x.Shp, y.Shp)) ->
  p =%> l
buildSupervisedLearningSystem f loss (xInput, yTrue) =
  let curriedParametricMap = uncurry f -- we're currying/uncurrying twice
      addInput = (hancockMap id (State xInput)) %>> curriedParametricMap
      addLoss = (hancockMap addInput (State yTrue)) %>> loss
      pruneUnits = rightUnitInv %>> rightUnitInv %>> addLoss
  in pruneUnits

public export
optimiseLearner : {p, x, y, l : AddCont} -> InterfaceOnPositions l Num =>
  (f : ParaAddDLens x y) ->
  (nonDep : IsNotDependent f) =>
  (loss : (y >< y) =%> l) ->
  (ioPair : IO (x.Shp, y.Shp)) ->
  (opt : Optimiser (GetParam f) stateTy) ->
  (currentValue : (GetParam f).Shp) -> (currentState : stateTy) ->
  (numSteps : Nat) ->
  Show (GetParam f).Shp => Show stateTy =>
  IO ((GetParam f).Shp, stateTy)
optimiseLearner f loss ioPair opt currentValue currentState numSteps = do
  (x, yTrue) <- ioPair
  let supervisedLearningSystem
    = buildSupervisedLearningSystem (toHomRepresentation f) loss (x, yTrue)
  optimise supervisedLearningSystem opt currentValue currentState numSteps


namespace AdditiveLenses
  %hide Data.Container.Base.Morphism.Definition.DependentLenses.(=%>)

  public export
  copyMul : Const Double =%> Const Double
  copyMul = Copy %>> Mul

  public export
  mulParametric : ParaAddDLens (Const Double) (Const Double)
  mulParametric = binaryOpToPara {p=Const Double} Mul

  public export
  mse : (Const Double >< Const Double) =%> (Const Double)
  mse = (hancockMap id Negate) %>> Sum %>> copyMul

  public export
  addParametric : ParaAddDLens (Const Double) (Const Double)
  addParametric = binaryOpToPara {p=Const Double} Sum

  public export
  affineParametric : ParaAddDLens (Const Double) (Const Double)
  affineParametric = composePara mulParametric addParametric

  public export
  affineHomForm : DepHancockProduct (Const Double) (\_ => Const Double) =%>
    (InternalLensAdditive (Const Double) (Const Double))
  affineHomForm = toHomRepresentation affineParametric @{MkNonDep ?aa ?bb}

public export
linRegData : IO (Double, Double)
linRegData = pure (1.0, 7.0)


public export
linearRegression : (startingParamsValue : (Double, Double)) ->
  (numSteps : Nat) ->
  IO (x : Double ** Double)
linearRegression (p1, p2) numSteps =
  let opt = GD {pType=Double} {lr=0.001}
  in fst <$> optimiseLearner {stateTy=Unit} affineParametric {nonDep = MkNonDep ?aa ?bb} mse linRegData ?oopt (p1 ** p2) () numSteps

public export
minimiseCopyMulGD : (startingValue : Double) ->
  (numSteps : Nat) ->
  IO Double
minimiseCopyMulGD startingValue numSteps =
  let opt = GD {pType=Double} {lr=0.001}
  in fst <$> optimise copyMul opt startingValue () numSteps

public export
minimiseCopyMulMomentum : (startingValue : Double) ->
  (numSteps : Nat) ->
  IO Double
minimiseCopyMulMomentum startingValue numSteps =
  let opt = GDMomentum {pType=Double} {lr=0.001} {gamma=0.9}
  in fst <$> optimise copyMul opt startingValue 0 numSteps


  


{-
||| If we want to write this for an arbitrary `D pType` we'd need the sharp
||| machinery from Diegetic open games
||| @lr is the learning rate, should be negative here since we are adding it
public export
sgd : Num pType => (lr : pType) -> Optimiser (Const pType)
sgd lr = MkOptimiser $ !% \p => (p ** \p' => p + lr * p')


{-
public export
DotTensor : {n: Nat} ->
  (Tensor [n] Double, Tensor [n] Double) -> Tensor [] Double
DotTensor (t1, t2) = dot t1 t2

public export
dotDifferentiable : {n : Nat} -> BwDifferentiable (DotTensor {n})
dotDifferentiable = MkBwDiff (\(t1, t2), dt =>
  ((\x => x * extract dt) <$> t2, (\x => x * extract dt) <$> t1))
