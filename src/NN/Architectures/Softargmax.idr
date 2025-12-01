module NN.Architectures.Softargmax

import Data.Tensor

||| Commonly known as 'softmax'
public export
softargmax : {i : Cont} -> Fractional a => Exp a =>
  (allAlg : AllAlgebra [i] a) =>
  {default 1 temperature : a} ->
  CTensor [i] a -> CTensor [i] a
softargmax {temperature} t
  = let exps : CTensor [i] a := exp <$> (t <&> (/ temperature))
    in exps <&> (/ (reduce exps))

-- TODO make softargmax a parametric function with temperature as the parameter



-- TODO namedSoftmax
-- namedSoftmax : {axis : Type -> Type}
--   -> {shape : Vect n ApplF} -> {a : Type}
--   -> Functor axis
--   => Elem axis shape
--   -> TensorA shape a
--   -> TensorA shape a
-- namedSoftmax {shape = []} axis t impossible -- can't be in vector if vector empty
-- namedSoftmax {shape = (axis :: ss)} Here (GTS x) = GTS (?sm <$> x)
-- namedSoftmax {shape = (s :: ss)} (There later) (GTS x) = GTS ?namedSoftmax_rhs_4
