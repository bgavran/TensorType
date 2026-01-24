module NN.Architectures.Transformer.Attention

import Data.Tensor
import Data.Para
import NN.Architectures.Softargmax

||| Generalised form of attention
public export
crossAttention : {a : Type} -> Num a =>
  {inputStructure, crossStructure, features : Axis} ->
  (acif : NewAxisConsistent inputStructure [features]) =>
  (accf : NewAxisConsistent crossStructure [features]) =>
  (acci : NewAxisConsistent crossStructure [inputStructure]) =>
  TensorMonoid inputStructure.cont => TensorMonoid features.cont =>
  (allAlg : AllAlgebra [inputStructure, features] a) =>
  {default id causalMask : Tensor [crossStructure, inputStructure] a ->
                           Tensor [crossStructure, inputStructure] a} ->
  (softargmax : Tensor [inputStructure] a ->
                Tensor [inputStructure] a) ->
  (q, v : Tensor [inputStructure, features] a) ->
  (k : Tensor [crossStructure, features] a) ->
  Tensor [crossStructure, features] a
crossAttention {allAlg=Cons {rest=xx}, causalMask} softargmax q v k =
  let attentionMatrix : Tensor [crossStructure, inputStructure] a
      attentionMatrix = q `matrixMatrixProduct` k
  in (softargmax <-$> (causalMask attentionMatrix)) `matMul` v

||| Self-attention is cross-attention where inputStructure = crossStructure
public export
selfAttention : {a : Type} -> Num a =>
  {inputStructure, features : Axis} ->
  NewAxisConsistent inputStructure [features] =>
  (TensorMonoid inputStructure.cont) =>
  (TensorMonoid features.cont) =>
  (allAlg : AllAlgebra [inputStructure, features] a) =>
  {default id causalMask : Tensor [inputStructure, inputStructure] a ->
                           Tensor [inputStructure, inputStructure] a} ->
  (softargmax : Tensor [inputStructure] a -> Tensor [inputStructure] a) ->
  (q, v, k : Tensor [inputStructure, features] a) ->
  Tensor [inputStructure, features] a
selfAttention {causalMask} = crossAttention {causalMask}

||| Data structure for holding parameters of self-attention
public export
record SelfAttentionParams (features : Axis) (a : Type) where
  constructor MkSAParams
  queryMatParam : Tensor [features, features] a
  valueMatParam : Tensor [features, features] a
  keyMatParam : Tensor [features, features] a

||| Forward pass of self-attention, from input
public export
SAImpl : {a : Type} -> Num a =>
  {inputStructure, features : Axis} ->
  (ac : NewAxisConsistent inputStructure [features]) =>
  (TensorMonoid inputStructure.cont) =>
  (TensorMonoid features.cont) =>
  (allAlg : AllAlgebra [inputStructure, features] a) =>
  {default id causalMask : Tensor [inputStructure, inputStructure] a ->
                           Tensor [inputStructure, inputStructure] a} ->
  (softargmax : Tensor [inputStructure] a -> Tensor [inputStructure] a) ->
  (input : Tensor [inputStructure, features] a) ->
  (params : SelfAttentionParams features a) ->
  Tensor [inputStructure, features] a
SAImpl {allAlg = Cons, causalMask}
  softargmax input (MkSAParams queryMat valueMat keyMat)
  = let queries = queryMat `matrixMatrixProduct` input
        keys = keyMat `matrixMatrixProduct` input
        values = valueMat `matrixMatrixProduct` input
    in selfAttention {causalMask} softargmax queries values keys

||| Self-attention as a parametric map
public export
SelfAttention : {a : Type} -> Num a =>
  {inputStructure, features : Axis} ->
  NewAxisConsistent inputStructure [features] =>
  (TensorMonoid inputStructure.cont) => (TensorMonoid features.cont) =>
  (allAlg : AllAlgebra [inputStructure, features] a) =>
  {default id causalMask : Tensor [inputStructure, inputStructure] a ->
                           Tensor [inputStructure, inputStructure] a} ->
  (softargmax : Tensor [inputStructure] a ->
                Tensor [inputStructure] a) ->
  Tensor [inputStructure, features] a -\-> Tensor [inputStructure, features] a
SelfAttention {causalMask} softargmax = MkPara
  (const (SelfAttentionParams features a))
  (SAImpl {causalMask} softargmax)

-- public export
-- SelfAttentionParams : (features : Nat) -> (a : Type) -> Type
-- SelfAttentionParams features a = CSelfAttentionParams (Vect features) a

public export
causalMask : {a : Type} -> Num a =>
  {c : Axis} -> Exp a =>
  InterfaceOnPositions c.cont MOrd =>
  TensorMonoid c.cont =>
  Tensor [c, c] a -> Tensor [c, c] a
causalMask attentionMatrix =
  let contShape : c.cont.Shp
      contShape = shapeExt (shapeExt (GetT attentionMatrix))
  in maskedFill attentionMatrix (not <$> cTriBool contShape) minusInfinity