module NN.Training.Examples

import Data.Tensor
import Data.Container.Additive
import NN.Optimisers.Definition
import NN.Optimisers.Instances
import NN.Training.Optimisation
import NN.Training.DataLoader
import NN.Utils
import Data.Para

namespace AdditiveLenses
  %hide Data.Container.Base.Morphism.Definition.DependentLenses.(=%>)

  public export
  MulParametric : ParaAddDLens (Const Double) (Const Double)
  MulParametric = binaryOpToPara {p=Const Double} Mul

  public export
  AddParametric : ParaAddDLens (Const Double) (Const Double)
  AddParametric = binaryOpToPara {p=Const Double} Sum

  public export
  AffineParametric : ParaAddDLens (Const Double) (Const Double)
  AffineParametric = composePara MulParametric AddParametric

public export
linearRegressionDataLoader : DataLoader Double Double
linearRegressionDataLoader = MkDataLoader 3 [
  (1, 5),
  (2, 9),
  (3, 13)]

public export
linearRegression : (f : ParaAddDLens (Const Double) (Const Double)) ->
  Num (GetParam f).Shp => Neg (GetParam f).Shp =>
  FromDouble (GetParam f).Shp => Show (GetParam f).Shp =>
  (isFlat : IsFlat (GetParam f)) =>
  (numSteps : Nat) ->
  IO (GetParam f).Shp
linearRegression f@(MkPara (MkAddCont (Const p)) _)
  {isFlat = MkIsFlat p @{mon}} numSteps =
  let opt = GD {pType=p} {lr=0.01} -- {gamma=0.9}
      dataLoader = sample linearRegressionDataLoader
  in fst <$> optimiseLearner f MSE dataLoader opt numSteps

public export
minimiseCopyMulGD : (startingValue : Double) ->
  (numSteps : Nat) ->
  IO Double
minimiseCopyMulGD startingValue numSteps =
  let opt = GD {pType=Double} {lr=0.001}
  in fst <$> optimise (pure $ Copy %>> Mul) opt numSteps

public export
minimiseCopyMulMomentum : (startingValue : Double) ->
  (numSteps : Nat) ->
  IO Double
minimiseCopyMulMomentum startingValue numSteps =
  let opt = GDMomentum {pType=Double} {lr=0.001} {gamma=0.9}
  in fst <$> optimise (pure $ Copy %>> Mul) opt numSteps

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