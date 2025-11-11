module Architectures.Transformer.Definition

import Data.Tensor
import Data.Para

import Architectures.Affine
import Architectures.Residual
import Architectures.MLP
import Architectures.Activations
import Architectures.Transformer.Attention
import Architectures.Utils

||| Single-head transformer layer
||| Only missing layernorm, otherwise a complete definition
public export
Transformer : {a : Type} -> Num a => Ord a =>
  {inputStructure, features : Cont} ->
  (allAppl : AllApplicative [inputStructure, features]) =>
  (allAlg : AllAlgebra [inputStructure, features] a) =>
  {default id causalMask : CTensor [inputStructure, inputStructure] a -> CTensor [inputStructure, inputStructure] a} ->
  (softargmax : CTensor [inputStructure] a -> CTensor [inputStructure] a) ->
  CTensor [inputStructure, features] a -\-> CTensor [inputStructure, features] a
Transformer {allAppl = Cons} {allAlg = Cons} softargmax
  = composePara (addResidual (SelfAttention softargmax)) (addResidual ffnet)
    where
      ffnet : CTensor [inputStructure, features] a -\-> CTensor [inputStructure, features] a
      ffnet = paraMapFirstAxis (multiLayerPerceptron {a=a} {ieva=features} 2 (trivialParam Tensor.relu) {lastLayerActivation=False}) 