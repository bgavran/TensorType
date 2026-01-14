module NN.Architectures.Softargmax

import Data.Tensor
import Data.Para

||| Numerically stable log-sum-exp operation
||| LSE(x) = max(x) + log(Σᵢ exp(xᵢ - max(x)))
||| See https://gregorygundersen.com/blog/2020/02/09/log-sum-exp/
public export
logSumExp : {i : Cont} -> Exp a => Ord a => Neg a =>
  Foldable (CTensor [i]) =>
  (allAlg : AllAlgebra [i] a) =>
  CTensor [i] a -> Maybe a
logSumExp t = do
  c <- max t
  pure $ c + log (reduce (t <&> (\x => exp $ x - c)))

||| Log(softargmax(x)), but computationally efficient and numerically stable
||| Used for computing cross-entropy loss
||| Returns empty tensor for empty input
public export
logSoftargmax : {i : Cont} -> Exp a => Ord a => Neg a =>
  Foldable (CTensor [i]) =>
  (allAlg : AllAlgebra [i] a) =>
  CTensor [i] a -> CTensor [i] a
logSoftargmax t = case logSumExp t of
  Just lse => t <&> (\x => x - lse) -- Non-empty: subtract LSE from each element
  Nothing  => t                     -- t is empty

||| Commonly known as 'softmax'
||| When `temperature=0` it reduces to `argmax`
public export
softargmaxImpl : {i : Cont} -> Fractional a => Exp a => Ord a => Neg a =>
  Foldable (CTensor [i]) =>
  (allAlg : AllAlgebra [i] a) =>
  {default 1 temperature : a} ->
  CTensor [i] a -> CTensor [i] a
softargmaxImpl {temperature} t = exp <$> logSoftargmax (t <&> (/ temperature))

||| Softargmax as a parametric map, with temperature as a parameter
public export
softargmax : {i : Cont} ->
  {a : Type} -> Fractional a => Exp a => Ord a => Neg a =>
  Foldable (CTensor [i]) =>
  (allAlg : AllAlgebra [i] a) =>
  CTensor [i] a -\-> CTensor [i] a
softargmax = MkPara 
  (\_ => a) -- temperature is the parameter
  (\t, temperature => softargmaxImpl {temperature} t)


inpp : Tensor [3] Double
inpp = ># [1000, 999, 998]

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
