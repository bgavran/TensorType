module Data.Autodiff.Ops

import System.Random

import Data.Tensor
import Data.Tensor.Utils
import Data.Container.Additive
import Data.Container.Additive.Quantifiers
import Data.Para
import Data.Autodiff.Model
import Control.Monad.Distribution
import Data.ComMonoid
import Data.Materialise

import Misc

%hide Data.Container.Base.Morphism.Definition.DependentLenses.(=%>)

{-------------------------------------------------------------------------------
This file contains the derivatives of various useful building blocks

Eventually will be combined with functionality which functorially assigns these
to any forward pass

-------------------------------------------------------------------------------}

public export
mulModel : {t : Type} -> Neg t => Random t =>
  Const t -\-> Const t
mulModel = fromPara (binaryOpToPara {p = Const t} mul) DefaultInit

public export
addModel : {t : Type} -> Neg t => Random t =>
  Const t -\-> Const t
addModel = fromPara (binaryOpToPara {p = Const t} sum) DefaultInit

public export
scalarAffine : {t : Type} -> Neg t => Random t => Materialise t =>
  Const t -\-> Const t
scalarAffine = mulModel >>> addModel

||| Apply a scalar lens elementwise across a tensor
public export
parallelTensor : {a, b : Type} -> Num a => Num b =>
  {shape : TensorShape rank} ->
  AllC TensorMonoid shape => AllC IsConcrete shape =>
  (f : Const a =%+> Const b) ->
  Const (Tensor shape a) =%+> Const (Tensor shape b)
parallelTensor f = !%+ \x =>
  let outs : Tensor shape (y : b ** (b -> a))
      outs = materialise ((%!+) f <$> x)
  in (materialise (fst <$> outs) ** \ys' => materialise [| snd outs ys' |])

||| `Tensor shape` applied to a model: one copy per entry, each with its own parameter
public export
parallelTensorModel : {a, b : Type} -> Num a => Num b =>
  {shape : TensorShape rank} -> AllC TensorMonoid shape => AllC IsConcrete shape =>
  Traversable (Tensor shape) =>
  (m : Const a -\-> Const b) -> Const (Tensor shape a) -\-> Const (Tensor shape b)
parallelTensorModel m = MkModel (Tensor shape m.Params) @{tensorComMonoid m.pMon}
  (sequence (pure m.init)) $
  !%+ \(x, ps) =>
    let outs : Tensor shape (y : b ** b -> (a, m.Params))
        outs = materialise ([| (x, ps) |] <&> (%!+) m.run)
    in (materialise (fst <$> outs) ** \ys' =>
      let grads : Tensor shape (a, m.Params)
          grads = materialise [| snd outs ys' |]
      in (fst <$> grads, snd <$> grads))

public export
copyN : {a : Type} -> Num a => {n : Nat} -> {axisName : AxisName} ->
  Const a =%+> Const (Tensor [axisName ~~> n] a)
copyN = !%+ \x => (pure x ** reduce)

public export
sameFromTensorN : {a, b : Type} -> Num a => Num b => {n : Nat} ->
  {axisName : AxisName} ->
  Traversable (Tensor [axisName ~~> n]) =>
  (m : Const a -\-> Const b) -> Const a -\-> Const (Tensor [axisName ~~> n] b)
sameFromTensorN m = precomposeLens copyN (parallelTensorModel m)

||| Dual to `copyN`
public export
sumAxis : {n : Axis} -> IsCubical n => Num a =>
  TensorMonoid n.cont =>
  Const (Tensor [n] a) =%+> Const (Tensor [] a)
sumAxis @{MkIsCubical _ n} = !%+ \t => (># reduce t ** \a' => fill (#> a'))

||| Divide by a constant, entrywise in both directions
public export
divBy : {a : Type} -> Num a => Fractional a =>
  (d : a) ->
  Const (Tensor [] a) =%+> Const (Tensor [] a)
divBy d = !%+ \x => (x <&> (/ d) ** \x' => x' <&> (/ d))

public export
meanSquaredDifference : IsCubical n => TensorMonoid n.cont =>
  {a : Type} -> Num a => Neg a => Fractional a => Cast Nat a =>
  Const (Tensor [n] a) >*< Const (Tensor [n] a) =%+> Const (Tensor [] a)
meanSquaredDifference @{MkIsCubical _ n}
  = SquaredDifference %+>> sumAxis %+>> divBy (cast n)

-- Activations

||| Recovers `ReLU` when `alpha=0`
||| Cannot be written as a composition of scaling and `ReLU`
public export
leakyReLU : {a : Type} -> Num a => Ord a =>
  (alpha : a) ->
  Const a =%+> Const a
leakyReLU alpha = !%+ \x =>
  (if x > 0 then x else alpha * x ** \x' => if x > 0 then x' else alpha * x')

public export
leakyReLUModel : {a : Type} -> Num a => Ord a =>
  (alpha : a) ->
  {shape : TensorShape rank} -> AllC TensorMonoid shape => AllC IsConcrete shape =>
  Const (Tensor shape a) -\-> Const (Tensor shape a)
leakyReLUModel alpha = trivialParam (parallelTensor (leakyReLU alpha))

public export
reluModel : {a : Type} -> Num a => Ord a =>
  {shape : TensorShape rank} -> AllC TensorMonoid shape => AllC IsConcrete shape =>
  Const (Tensor shape a) -\-> Const (Tensor shape a)
reluModel = leakyReLUModel 0

-- Distributions

||| Interpret a vector as logits of a distribution. The backward pass is
||| identity: gradients are computed in the sme way
public export
fromLogits : {0 name : AxisName} -> {0 n : Nat} ->
  Const (Tensor [name ~~> n] Double) =%+> Simplex name n
fromLogits = !%+ \xs => (MkDist xs ** id)

public export
fromLogitsModel : {0 name : AxisName} -> {0 n : Nat} ->
  Const (Tensor [name ~~> n] Double) -\-> Simplex name n
fromLogitsModel = trivialParam fromLogits
