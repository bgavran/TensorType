module NN.Architectures.Utils

import Data.Para
import Data.Tensor

||| Batching only works simply when we have a non-dependent Para
public export
paraMapFirstAxis : {c : Axis} ->
  {cs : TensorShape rank} -> {ds : TensorShape rank'} ->
  NewAxisConsistent c cs => NewAxisConsistent c ds =>
  Num a =>
  (pf : Tensor cs a -\-> Tensor ds a) ->
  (nonDep : IsNotDependent pf) =>
  Tensor (c :: cs) a -\-> Tensor (c :: ds) a
paraMapFirstAxis (MkPara (const pType) f) {nonDep = MkNonDep pType f} = MkPara
  (\_ => pType) (\t, p => flip f p <-$> t)
