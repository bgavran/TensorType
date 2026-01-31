module NN.Architectures.Utils

import Data.Para
import Data.Tensor

||| Batching only works simply when we have a non-dependent Para
public export
paraMapFirstAxis : {cs : List Cont} -> Num a => All TensorMonoid cs =>
  (pf : CTensor cs a -\-> CTensor ds a) ->
  (nonDep : IsNotDependent pf) =>
  CTensor (c :: cs) a -\-> CTensor (c :: ds) a
paraMapFirstAxis (MkPara (const pType) f) {nonDep = MkNonDep pType f} = MkPara
  (\_ => pType) (\t, p => flip f p <-$> t)
