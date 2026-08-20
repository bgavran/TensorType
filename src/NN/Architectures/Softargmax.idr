module NN.Architectures.Softargmax

import Data.Tensor
import Data.Para

import public Data.Tensor.Softargmax

||| Softargmax as a parametric map, with temperature as a parameter
||| The underlying implementation lives in `Data.Tensor.Softargmax`
||| TODO since distribution is an applicative functor (https://glaive-research.org/2025/02/11/Generalized-Transformers-from-Applicative-Functors.html)
||| is there a meaningful notion of the "distribution container"?
||| Is there a sense in which `Dist` is a functor on containers?
public export
softargmax : {i : Axis} ->
  {a : Type} -> Fractional a => Exp a => Ord a => Neg a =>
  IsFoldable i.cont =>
  (allAlg : AllAlgebra [i] a) =>
  Tensor [i] a -\-> Tensor [i] a
softargmax = MkPara 
  (\_ => a) -- temperature is the parameter
  (\(t ** temperature) => softargmaxImpl {temperature} t)
