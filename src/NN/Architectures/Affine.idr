module NN.Architectures.Affine

import Data.Tensor
import Data.Para

-- This is often called a 'linear layer', but really it is affine because of the bias

public export
record AffineLayerParams
  (x, y : Cont)
  (nx, ny : String)
  {auto ac : AllConsistent [ny, nx] [y, x]}
  (a : Type) where
  constructor MkParams
  weights : CTensor [y, x] [ny, nx] a
  bias : CTensor [y] [ny] a

public export
affineImpl : {x, y : Cont} ->
  {nx, ny : String} ->
  AllConsistent [ny, nx] [y, x] =>
  Num a =>
  AllAlgebra [x] [nx] a =>
  TensorMonoid x => TensorMonoid y =>
  CTensor [x] [nx] a -> AffineLayerParams x y nx ny a -> CTensor [y] [ny] a
affineImpl input (MkParams weights bias)
  = matrixVectorProduct weights input + bias

public export
affinePara : {x, y : Cont} -> {a : Type} -> Num a =>
  {nx, ny : String} ->
  AllConsistent [ny, nx] [y, x] =>
  AllAlgebra [x] [nx] a =>
  TensorMonoid x => TensorMonoid y =>
  CTensor [x] [nx] a -\-> CTensor [y] [ny] a
affinePara = MkPara
  (const (AffineLayerParams x y nx ny a))
  affineImpl
