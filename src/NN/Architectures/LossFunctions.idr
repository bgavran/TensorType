module NN.Architectures.LossFunctions

import Data.List
import Data.Fin
import Data.Vect
import Data.Zippable

import Data.Tensor
import Data.Tensor.Utils
import Data.Container.Additive
import Data.Autodiff.Ops
import Control.Monad.Distribution

import Data.Container.Additive.Quantifiers

import Data.Para

%hide Data.Container.Base.Morphism.Definition.DependentLenses.(=%>)

||| A loss is a parametric map whose parameter is the label
||| It is not a `Model` because there is no concept of initialisation
public export
Loss : (y, l : AddCont) -> Type
Loss y l = y =\\=> l

namespace Combinators
  ||| Run two losses in parallel, add their results
  public export
  pairLossFunctions : {y, z : AddCont} -> {l : Type} -> Num l =>
    Loss y (Const l) -> Loss z (Const l) -> Loss (y >*< z) (Const l)
  pairLossFunctions f g = postcomposeLens (composeParallel f g) sum

  ||| The loss of a coproduct of choices. When the types don't match, gradient
  ||| is infinite. In our examples we don't expect this to happen; but loss type
  ||| should be refined to exclude it eventually
  public export
  chosenBranchLoss : {n : Nat} -> {branches : Vect n AddCont} ->
    {default branches labels : Vect n AddCont} ->
    {0 lc : AddCont} -> Fractional lc.Shp =>
    (losses : (i : Fin n) -> index i branches >*< index i labels =%+> lc) ->
    Loss (Coproduct branches) lc
  chosenBranchLoss losses = MkPara (Coproduct labels) $
    !%+ \((i ** x), (j ** y)) => case decEq i j of
      Yes Refl => (%!+) (losses i) (x, y)
      No _ => (1 / 0 ** \_ => ((index i branches).Zero x, (index j labels).Zero y))

  ||| The loss variant of `resolveByLabel`. Given a loss on resolved choices we
  ||| can produce a loss on an effectful output, where the ground-truth label
  ||| selects the effect
  ||| This means that the training loop does not need to handle any effects 
  ||| anymore
  public export
  resolveLoss : {distName : AxisName} -> {n : Nat} ->
    {branches : Vect n AddCont} ->
    {0 l : AddCont} ->
    (ChoiceMade distName branches >*< ChoiceMade distName branches =%+> l) ->
    Loss (ProbabilisticChoice distName branches) l
  resolveLoss loss = MkPara
    (ChoiceMade distName branches)
    (resolveByLabel %+>> loss)

namespace Instances
  public export
  SquaredError : {a : Type} -> Num a => Neg a => Loss (Const a) (Const a)
  SquaredError = MkPara (Const a) SquaredDifference

  public export
  MeanSquaredError : {n : Axis} -> IsCubical n => TensorMonoid n.cont =>
    {a : Type} -> Num a => Neg a => Fractional a => Cast Nat a =>
    Loss (Const (Tensor [n] a)) (Const (Tensor [] a))
  MeanSquaredError = MkPara (Const (Tensor [n] a)) meanSquaredDifference

  ||| The payoff object is the rank-0 tensor, not `Double`
  public export
  softargmaxCrossEntropyLogits : {name : AxisName} -> {n : Nat} ->
    Simplex name n >*< Simplex name n =%+> Const (Tensor [] Double)
  softargmaxCrossEntropyLogits = !%+ \(predicted, labels) =>
    let logSoftargmaxLogits = logSoftargmax predicted.logits
        targetProbs = softargmaxImpl labels.logits
        out = - dot logSoftargmaxLogits targetProbs
    in (out ** \l' =>
      ((extract l' *) <$> (Prelude.exp <$> logSoftargmaxLogits) - targetProbs,
        fill 0)) -- zeros for now

  public export
  SoftargmaxCrossEntropyLogits : {name : AxisName} -> {n : Nat} ->
    Loss (Simplex name n) (Const (Tensor [] Double))
  SoftargmaxCrossEntropyLogits
    = MkPara (Simplex name n) softargmaxCrossEntropyLogits
