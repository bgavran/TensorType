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

||| A loss is a parametric map whose parameter is the label
||| It is not a `Model` because there is no concept of initialisation
public export
Loss : (y, l : AddCont) -> Type
Loss y l = y =\\=> l

||| The "parameter" object of the loss function is the type of supervised
||| learning labels
public export
Label : Loss y l -> Type
Label loss = (Param loss).Shp

namespace Combinators
  ||| Run two losses in parallel, add their results
  public export
  pairLossFunctions : {y, z : AddCont} -> {l : Type} -> Num l =>
    Loss y (Const l) -> Loss z (Const l) -> Loss (y >*< z) (Const l)
  pairLossFunctions f g = postcomposeLens (composeParallel f g) sum

  ||| The loss of a section against a labelled branch
  ||| We always choose the branch the label chooses
  public export
  chosenBranchLoss : {c : Cont} -> {branches : c.filledWith AddCont} ->
    {0 l : AddCont} ->
    (losses : (i : c.Pos (shapeExt branches)) -> Loss (index branches i) l) ->
    Loss (Section (index branches)) l
  chosenBranchLoss losses = MkPara (AddContDPair (\i => Param (losses i)))
    (evalSection {a = index branches} {p = \i => Param (losses i)}
      %+>> copair (\i => Run (losses i)))

  ||| Same as above, except we take an already chosen branch, and fail if 
  ||| label disagrees with it
  public export
  matchedBranchLoss : {c : Cont} -> (dec : IsDecidable c) =>
    {branches : c.filledWith AddCont} -> {0 l : AddCont} ->
    (losses : (i : c.Pos (shapeExt branches)) -> Loss (index branches i) l) ->
    Loss (Coproduct branches) (Maybe l)
  matchedBranchLoss losses = MkPara (AddContDPair (\i => Param (losses i)))
    (matchIndex @{GetInterface dec (shapeExt branches)}
      {b = index branches} {l = \i => Param (losses i)}
      %+>> Maybe (copair (\i => Run (losses i))))


  ||| Given a made choice, pair with with a dirac delta distribution
  public export
  madeChoice : {ax : Axis} -> IsNaperian ax => DecEq (Log ax) =>
    {f : Log ax -> AddCont} ->
    AddContDPair f =%+> Simplex ax >*< AddContDPair f
  madeChoice = !%+ \ix => ((diracDelta (fst ix), ix) ** snd)

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
  ||| Defined for Naperian axes, where the prediction and the label have one shape
  ||| TODO the prediction and the label can be distributions of different shapes!
  public export
  softargmaxCrossEntropyLogits : {a : Axis} ->
    (nap : IsNaperian a) => IsFoldable a.cont =>
    Simplex a >*< Simplex a =%+> Const (Tensor [] Double)
  softargmaxCrossEntropyLogits @{MkIsNaperian _ pos} = !%+ \(predicted, labels) =>
    let logSoftargmaxLogits = logSoftargmax predicted.logits
        targetProbs = softargmaxImpl labels.logits
        out = - dot logSoftargmaxLogits targetProbs
    in (out ** \l' =>
      ((extract l' *) <$> (Prelude.exp <$> logSoftargmaxLogits) - targetProbs,
       -- the derivative in the label's logits, though training discards it
       (extract l' *) <$> negate (targetProbs * ((+ extract out) <$> logSoftargmaxLogits))))

  public export
  SoftargmaxCrossEntropyLogits : {a : Axis} ->
    IsNaperian a => IsFoldable a.cont =>
    Loss (Simplex a) (Const (Tensor [] Double))
  SoftargmaxCrossEntropyLogits
    = MkPara (Simplex a) softargmaxCrossEntropyLogits
