module NN.Architectures.Affine

import System.Random

import Data.Tensor
import Data.Para
import Data.ComMonoid
import Data.Container.Additive
import Data.Autodiff.Model

-- This is often called a 'linear layer', but really it is affine because of the bias

||| A weight matrix and a bias vector
public export
AffineParams : (x, y : Axis) -> y `ConsistentWith` [x] =>
  Type -> Type
AffineParams x y a = (Tensor [y, x] a, Tensor [y] a)

public export
affineImpl : {x, y : Axis} ->
  y `ConsistentWith` [x] =>
  Num a =>
  AllAlgebra [x] a =>
  TensorMonoid x.cont => TensorMonoid y.cont =>
  DPair (Tensor [x] a) (const (AffineParams x y a)) -> Tensor [y] a
affineImpl (input ** (weights, bias))
  = matrixVectorProduct weights input + bias

public export
affinePara : {x, y : Axis} -> {a : Type} -> Num a =>
  y `ConsistentWith` [x] =>
  AllAlgebra [x] a =>
  TensorMonoid x.cont => TensorMonoid y.cont =>
  Tensor [x] a -\-> Tensor [y] a
affinePara = MkPara
  (const (AffineParams x y a))
  affineImpl

public export
affineModel : {x, y : Axis} -> {a : Type} ->
  Neg a =>
  y `ConsistentWith` [x] =>
  AllAlgebra [x] a =>
  TensorMonoid x.cont => TensorMonoid y.cont =>
  Algebra (Ext y.cont) (Tensor [x] a) =>
  Random (Tensor [y, x] a) => Random (Tensor [y] a) =>
  Const (Tensor [x] a) -\-> Const (Tensor [y] a)
affineModel = layer (AffineParams x y a)
  [| MkPair (randomRIO (-1, 1)) (randomRIO (-1, 1)) |]
  (\input, (weights, bias) =>
    (matrixVectorProduct weights input + bias ** \dy =>
      (vectorMatrixProduct dy weights, (outer dy input, dy))))
