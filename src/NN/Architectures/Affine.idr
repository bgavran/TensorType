module NN.Architectures.Affine

import Data.Tensor
import Data.Para

-- This is often called a 'linear layer', but really it is affine because of the bias

public export
record AffineLayerParams
  (x, y : Axis)
  {auto ac : NewAxisConsistent y [x]}
  (a : Type) where
  constructor MkParams
  weights : Tensor [y, x] a
  bias : Tensor [y] a

public export
affineImpl : {x, y : Axis} ->
  NewAxisConsistent y [x] =>
  Num a =>
  AllAlgebra [x] a =>
  TensorMonoid x.cont => TensorMonoid y.cont =>
  Tensor [x] a -> AffineLayerParams x y a -> Tensor [y] a
affineImpl input (MkParams weights bias)
  = matrixVectorProduct weights input + bias

public export
affinePara : {x, y : Axis} -> {a : Type} -> Num a =>
  NewAxisConsistent y [x] =>
  AllAlgebra [x] a =>
  TensorMonoid x.cont => TensorMonoid y.cont =>
  Tensor [x] a -\-> Tensor [y] a
affinePara = MkPara
  (const (AffineLayerParams x y a))
  affineImpl
