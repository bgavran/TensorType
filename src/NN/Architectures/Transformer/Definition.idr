module NN.Architectures.Transformer.Definition

import Data.Tensor
import Data.Para

import NN.Architectures.Affine
import NN.Architectures.Residual
import NN.Architectures.MLP
import NN.Architectures.Activations
import NN.Architectures.Transformer.Attention
import NN.Architectures.Utils

||| Single-head transformer layer
||| Only missing layernorm, otherwise a complete definition
public export
Transformer : {a : Type} -> Num a => Ord a =>
  {inputStructure, features : Axis} ->
  (ac : AxesConsistent [inputStructure, features]) =>
  (TensorMonoid inputStructure.ToCont) =>
  (TensorMonoid features.ToCont) =>
  (allAlg : AllAlgebra [inputStructure, features] a) =>
  {default id causalMask : Tensor [inputStructure, inputStructure] a ->
                           Tensor [inputStructure, inputStructure] a} ->
  (softargmax : Tensor [inputStructure] a -> Tensor [inputStructure] a) ->
  Tensor [inputStructure, features] a -\-> Tensor [inputStructure, features] a
Transformer {ac  = _ :: [NewAxis NotInEmptyVect],
             allAlg = Cons} softargmax
  = composePara (addResidual (SelfAttention softargmax)) (addResidual ffnet)
    where
      ffnet : Tensor [inputStructure, features] a -\-> Tensor [inputStructure, features] a
      ffnet = paraMapFirstAxis (multiLayerPerceptron {a=a} {ieva=features} 2 (trivialParam relu) {lastLayerActivation=False})
