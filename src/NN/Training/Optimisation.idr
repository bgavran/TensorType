module NN.Training.Optimisation

import Data.Tensor
import Data.Container.Additive
import NN.Optimisers.Definition
import NN.Optimisers.Instances

||| Working with a non-dependent optimiser
||| Updates both the parameter and the internal state of an optimiser
public export
optimiseStep : {p, x : AddCont} -> InterfaceOnPositions x Num =>
  (f : p =%> x) ->
  (optimiser : Optimiser p stateTy) ->
  (p.Shp, stateTy) -> (p.Shp, stateTy) -- parameter update function
optimiseStep f (MkOptimiser opt) = fromCostate $ 
  opt %>> ULens (f %>> constantOne {c=x})

public export
runActionUntilMaxSteps : Show a =>
  (action : a -> IO a) ->
  (maxSteps : Nat) ->
  (currentStep : Nat) -> (currentValue : a) ->
  IO a
runActionUntilMaxSteps action maxSteps currentStep currentValue
  = case currentStep < maxSteps of
    True => do
      result <- action currentValue
      putStrLn "Current step: \{show currentStep}, value: \{show result}"
      runActionUntilMaxSteps action maxSteps (currentStep + 1) result
    False => do
      putStrLn "Max steps (\{show maxSteps}) reached. Final value: \{show currentValue}"
      pure currentValue

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
minimiseCopyMulGD : (startingValue : Double) ->
  (numSteps : Nat) ->
  IO Double
minimiseCopyMulGD startingValue numSteps =
  let opt = GD {pType=Double} {lr=0.001}
  in fst <$> minimiseFn (Copy %>> Mul) opt startingValue () numSteps

public export
minimiseCopyMulMomentum : (startingValue : Double) ->
  (numSteps : Nat) ->
  IO Double
minimiseCopyMulMomentum startingValue numSteps =
  let opt = GDMomentum {pType=Double} {lr=0.001} {gamma=0.9}
  in fst <$> minimiseFn (Copy %>> Mul) opt startingValue 0 numSteps


  


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
