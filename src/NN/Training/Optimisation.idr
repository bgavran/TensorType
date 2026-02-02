module NN.Training.Optimisation

import Data.Tensor
import Data.Container.Additive
import NN.Optimisers.Definition
import NN.Optimisers.Instances
import NN.Training.Utils
import Data.Para

||| Working with a non-dependent optimiser
||| Here we update both the parameter and the internal state of an optimiser
public export
optimiseStep : {p, x : AddCont} -> InterfaceOnPositions x Num =>
  (f : p =%> x) ->
  (optimiser : Optimiser p stateTy) ->
  (p.Shp, stateTy) -> (p.Shp, stateTy) -- parameter update function
optimiseStep f (MkOptimiser opt) = fromCostate $ 
  opt %>> ULens (f %>> constantOne {c=x})

public export
minimiseFn : {p, x : AddCont} -> InterfaceOnPositions x Num =>
  Show p.Shp => Show stateTy =>
  (f : p =%> x) ->
  (opt : Optimiser p stateTy) ->
  (currentValue : p.Shp) -> (currentState : stateTy) ->
  (numSteps : Nat) ->
  IO (p.Shp, stateTy)
minimiseFn f opt currentValue currentState numSteps = runActionUntilMaxSteps
  (\(currVal, currState) => pure $ optimiseStep f opt (currVal, currState))
  numSteps
  0
  (currentValue, currentState)


public export
optimiserLearnerStep : {p, x, y : AddCont} ->
  (f : p =%> InternalLensAdditive x y) ->
  (costate : InternalLensAdditive x y =%> Scalar) ->
  (optimiser : Optimiser p stateTy) ->
  (p.Shp, stateTy) -> (p.Shp, stateTy) -- parameter update function
optimiserLearnerStep f costate (MkOptimiser opt) = fromCostate $
  opt %>> ULens (f %>> costate)

public export
optimiseLearner : {p, x, y, l : AddCont} -> InterfaceOnPositions l Num =>
  Show p.Shp => Show stateTy =>
  (f : p =%> InternalLensAdditive x y) ->
  (loss : (y >< y) =%> l) ->
  (ioPair : IO (x.Shp, y.Shp)) ->
  (opt : Optimiser p stateTy) ->
  (currentValue : p.Shp) -> (currentState : stateTy) ->
  (numSteps : Nat) ->
  IO (p.Shp, stateTy)
optimiseLearner f loss ioPair opt currentValue currentState numSteps = do
  (x, yTrue) <- ioPair
  let ff = (hancockMap id (State x)) %>> uncurry f
      paired = (hancockMap ff (State yTrue)) %>> loss
      pruned = rightUnitInv %>> rightUnitInv %>> paired
  minimiseFn pruned opt currentValue currentState numSteps

namespace AdditiveLenses
  %hide Data.Container.Base.Morphism.Definition.DependentLenses.(=%>)

  public export
  copyMul : Const Double =%> Const Double
  copyMul = Copy %>> Mul

  public export
  mulParametric : ParaAddDLens (Const Double) (Const Double)
  mulParametric = binaryOpToPara {p=Const Double} Mul

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
minimiseCopyMulGD : (startingValue : Double) ->
  (numSteps : Nat) ->
  IO Double
minimiseCopyMulGD startingValue numSteps =
  let opt = GD {pType=Double} {lr=0.001}
  in fst <$> minimiseFn copyMul opt startingValue () numSteps

public export
minimiseCopyMulMomentum : (startingValue : Double) ->
  (numSteps : Nat) ->
  IO Double
minimiseCopyMulMomentum startingValue numSteps =
  let opt = GDMomentum {pType=Double} {lr=0.001} {gamma=0.9}
  in fst <$> minimiseFn copyMul opt startingValue 0 numSteps


  


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
