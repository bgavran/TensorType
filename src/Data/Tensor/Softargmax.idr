module Data.Tensor.Softargmax

import Data.Tensor.Tensor
import Data.Tensor.Utils

{-------------------------------------------------------------------------------
Used by both `Control.Monad.Distribution` and `NN.Architetures.Softargmax`
-------------------------------------------------------------------------------}

||| Numerically stable log-sum-exp operation
||| LSE(x) = max(x) + log(Σᵢ exp(xᵢ - max(x)))
||| See https://gregorygundersen.com/blog/2020/02/09/log-sum-exp/
public export
logSumExp : {i : Axis} -> Exp a => Ord a => Neg a =>
  Foldable (Tensor [i]) =>
  Tensor [i] a -> Maybe a
logSumExp t = do
  c <- max t
  pure $ c + log (reduce @{algebraFoldable} (t <&> (\x => exp $ x - c)))

||| Log(softargmax(x)), but computationally efficient and numerically stable
||| Used for computing cross-entropy loss
||| Returns empty tensor for empty input
public export
logSoftargmax : {i : Axis} -> Exp a => Ord a => Neg a =>
  Foldable (Tensor [i]) =>
  Tensor [i] a -> Tensor [i] a
logSoftargmax t = case logSumExp t of
  Just lse => t <&> (\x => x - lse) -- Non-empty: subtract LSE from each element
  Nothing  => t                     -- t is empty

||| Commonly known as 'softmax'
||| As `temperature->0` it reduces to `argmax`
||| TODO fix numerics when temperature=0
public export
softargmaxImpl : {i : Axis} -> Fractional a => Exp a => Ord a => Neg a =>
  IsFoldable i .cont =>
  {default 1 temperature : a} ->
  Tensor [i] a -> Tensor [i] a
softargmaxImpl {temperature} t
  = exp <$> logSoftargmax (t <&> (/ temperature))
