module NN.Architectures.Transformer.Attention

import Data.Tensor
import Data.Para
import NN.Architectures.Softargmax

||| Generalised form of attention
public export
crossAttention : {a : Type} -> Num a =>
  {inputStructure, crossStructure, features : Cont} ->
  (TensorMonoid features) =>
  (TensorMonoid inputStructure) =>
  (allAlg : AllAlgebra [inputStructure, features] a) =>
  {default id causalMask : CTensor [crossStructure, inputStructure] a -> CTensor [crossStructure, inputStructure] a} ->
  (softargmax : CTensor [inputStructure] a -> CTensor [inputStructure] a) ->
  (q, v : CTensor [inputStructure, features] a) ->
  (k : CTensor [crossStructure, features] a) ->
  CTensor [crossStructure, features] a
crossAttention {allAlg=Cons} {causalMask} softargmax q v k =
  let attentionMatrix : CTensor [crossStructure, inputStructure] a
      attentionMatrix = (q `matrixMatrixProduct` k)
  in (softargmax <-$> (causalMask attentionMatrix)) `matMul` v

||| Self-attention is cross-attention where inputStructure = crossStructure
public export
selfAttention : {a : Type} -> Num a =>
  {inputStructure, features : Cont} ->
  (TensorMonoid inputStructure) =>
  (TensorMonoid features) =>
  (allAlg : AllAlgebra [inputStructure, features] a) =>
  {default id causalMask : CTensor [inputStructure, inputStructure] a -> CTensor [inputStructure, inputStructure] a} ->
  (softargmax : CTensor [inputStructure] a -> CTensor [inputStructure] a) ->
  (q, v, k : CTensor [inputStructure, features] a) ->
  CTensor [inputStructure, features] a
selfAttention {causalMask} = crossAttention {causalMask}

||| Data structure for holding parameters of self-attention
public export
record CSelfAttentionParams (features : Cont) (a : Type) where
  constructor MkCSAParams
  queryMatParam : CTensor [features, features] a
  valueMatParam : CTensor [features, features] a
  keyMatParam : CTensor [features, features] a

||| Forward pass of self-attention, from input
public export
SAImpl : {a : Type} -> Num a =>
  {inputStructure, features : Cont} ->
  (TensorMonoid inputStructure) =>
  (TensorMonoid features) =>
  (allAlg : AllAlgebra [inputStructure, features] a) =>
  {default id causalMask : CTensor [inputStructure, inputStructure] a -> CTensor [inputStructure, inputStructure] a} ->
  (softargmax : CTensor [inputStructure] a -> CTensor [inputStructure] a) ->
  (input : CTensor [inputStructure, features] a) ->
  (params : CSelfAttentionParams features a) ->
  CTensor [inputStructure, features] a
SAImpl {allAlg = Cons} {causalMask} softargmax input (MkCSAParams queryMat valueMat keyMat)
  = let queries = queryMat `matrixMatrixProduct` input
        keys = keyMat `matrixMatrixProduct` input
        values = valueMat `matrixMatrixProduct` input
    in selfAttention {causalMask} softargmax queries values keys

||| Self-attention as a parametric map
public export
SelfAttention : {a : Type} -> Num a =>
  {inputStructure, features : Cont} ->
  (TensorMonoid inputStructure) =>
  (TensorMonoid features) =>
  (allAlg : AllAlgebra [inputStructure, features] a) =>
  {default id causalMask : CTensor [inputStructure, inputStructure] a -> CTensor [inputStructure, inputStructure] a} ->
  (softargmax : CTensor [inputStructure] a -> CTensor [inputStructure] a) ->
  CTensor [inputStructure, features] a -\-> CTensor [inputStructure, features] a
SelfAttention {causalMask} softargmax = MkPara
  (const (CSelfAttentionParams features a))
  (SAImpl {causalMask} softargmax)

public export
SelfAttentionParams : (features : Nat) -> (a : Type) -> Type
SelfAttentionParams features a = CSelfAttentionParams (Vect features) a

public export
causalMask : {a : Type} -> Num a =>
  {c : Cont} -> Exp a =>
  InterfaceOnPositions c MOrd =>
  TensorMonoid c =>
  CTensor [c, c] a -> CTensor [c, c] a
causalMask attentionMatrix =
  let contShape : c.Shp
      contShape = shapeExt (shapeExt (GetT attentionMatrix))
  in maskedFill attentionMatrix (not <$> cTriBool contShape) minusInfinity
