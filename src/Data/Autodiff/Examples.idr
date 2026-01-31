module Data.Autodiff.Examples

import Data.Autodiff.Core

%hide Data.Container.Object.Instances.Const
-- Some common maps and their backward derivatives

public export
State : {0 c : AddCont} -> (x : c.Shp) -> Scalar =%> c
State x = !%+ \() => (x ** \_ => ())

public export
Costate : {0 c : AddCont} ->
  (s : (x : c.Shp) -> c.Pos x) ->
  c =%> Scalar
Costate s = !%+ \x => (() ** \() => s x)

public export
Copy : {c : AddCont} ->
  c =%> (c >< c)
Copy = !%+ \x => ((x, x) ** uncurry (c.Plus x))

public export
Delete : {c : AddCont} ->
  c =%> Scalar
Delete = !%+ \x => (() ** \() => c.Zero x)

public export
Sum : Num a =>
  (Const a >< Const a) =%> Const a
Sum = !%+ \(x1, x2) => (x1 + x2 ** \x' => (x', x'))

public export
Zero : Num a =>
  Scalar =%> Const a
Zero = State 0

public export
Mul : Num a =>
  (Const a >< Const a) =%> Const a
Mul = !%+ \(x1, x2) => (x1 * x2 ** \x' => (x' * x2, x' * x1))

{-
public export
record Optimiser (param : AddCont) where
  constructor MkOptimiser
  ||| Notably, this is an ordinary dependent lens, not an additive one
  Opt : Const param.Shp =%> UC param

||| If we want to write this for an arbitrary `D pType` we'd need the sharp
||| machinery from Diegetic open games
||| @lr is the learning rate, should be negative here since we are adding it
public export
sgd : Num pType => (lr : pType) -> Optimiser (Const pType)
sgd lr = MkOptimiser $ !% \p => (p ** \p' => p + lr * p')

public export
minimiseFnStep : (fLens : Const Double =%> Const Double) ->
  (opt : Optimiser (Const Double)) ->
  (currentValue : Double) ->
  Double -- result
minimiseFnStep (!% fLens) (MkOptimiser opt) currentValue
  = (opt %>> fLens).bwd currentValue 1.0


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
minimiseFn : (fLens : Const Double =%> Const Double) ->
  (opt : Optimiser (Const Double)) ->
  (currentValue : Double) ->
  (numSteps : Nat) ->
  IO Double
minimiseFn fLens opt currentValue numSteps = runActionUntilMaxSteps
  (\currVal => pure $ minimiseFnStep fLens opt currVal)
  numSteps
  0
  currentValue

public export
minimiseCopyMul : (startingValue : Double) ->
  (numSteps : Nat) ->
  IO Double
minimiseCopyMul = minimiseFn (Copy %>> Mul) (sgd {pType=Double} (-0.001))


{-
public export
DotTensor : {n: Nat} ->
  (Tensor [n] Double, Tensor [n] Double) -> Tensor [] Double
DotTensor (t1, t2) = dot t1 t2

public export
dotDifferentiable : {n : Nat} -> BwDifferentiable (DotTensor {n})
dotDifferentiable = MkBwDiff (\(t1, t2), dt =>
  ((\x => x * extract dt) <$> t2, (\x => x * extract dt) <$> t1))