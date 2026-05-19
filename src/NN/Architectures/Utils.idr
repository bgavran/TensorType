module NN.Architectures.Utils

import Data.Para
import Data.Tensor

||| Batching only works simply when we have a non-dependent Para
public export
paraMapFirstAxis : {c : Axis} ->
  {cs : TensorShape rank} -> {ds : TensorShape rank'} ->
  c `ConsistentWith` cs => c `ConsistentWith` ds =>
  Num a =>
  (pf : Tensor cs a -\-> Tensor ds a) ->
  (nonDep : IsNotDependent pf) =>
  Tensor (c :: cs) a -\-> Tensor (c :: ds) a
paraMapFirstAxis (MkPara (const pType) f) {nonDep = MkNonDep pType f} = MkPara
  (\_ => pType) (\(t ** p) => flip (curry f) p <-$> t)