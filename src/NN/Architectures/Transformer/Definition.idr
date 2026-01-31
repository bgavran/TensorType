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
  {inputStructure, features : Cont} ->
  (TensorMonoid inputStructure) =>
  (TensorMonoid features) =>
  (allAlg : AllAlgebra [inputStructure, features] a) =>
  {default id causalMask : CTensor [inputStructure, inputStructure] a -> CTensor [inputStructure, inputStructure] a} ->
  (softargmax : CTensor [inputStructure] a -> CTensor [inputStructure] a) ->
  CTensor [inputStructure, features] a -\-> CTensor [inputStructure, features] a
Transformer {allAlg = Cons} softargmax
  = composePara (addResidual (SelfAttention softargmax)) (addResidual ffnet)
    where
      ffnet : CTensor [inputStructure, features] a -\-> CTensor [inputStructure, features] a
      ffnet = paraMapFirstAxis (multiLayerPerceptron {a=a} {ieva=features} 2 (trivialParam relu) {lastLayerActivation=False})
