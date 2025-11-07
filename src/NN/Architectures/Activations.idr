module NN.Architectures.Activations

import Data.Tensor
import Data.Para
import Misc

-- Should this be a typeclass?
public export
relu : Ord a => Num a => a -> a
relu x = max 0 x

public export
sigmoid : Fractional a => Exp a => a -> a
sigmoid x = ex / (1 + ex) where ex = exp x


namespace Tensor
  public export
  relu : Ord a => Num a => {names : Vect rank String} -> {shape : Vect rank Cont} -> AllConsistent names shape =>
    CTensor shape names a -> CTensor shape names a
  relu t = relu <$> t
 
  public export
  sigmoid : Fractional a => Exp a =>  {0 names : Vect rank String} ->
    {0 shape : Vect rank Cont} ->
    AllConsistent names shape =>
    CTensor shape names a -> CTensor shape names a
  sigmoid t = sigmoid <$> t
