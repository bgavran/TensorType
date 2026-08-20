module Control.Monad.Sample.Definition

import Data.Fin

import Data.Container.Base
import Data.Tensor
import Control.Monad.Distribution

||| Interface for sampling from a distribution
||| We require that there is at least one element in the distribution
||| TODO add temperature as a implicit parameter with a defualt value of 1.0
public export
interface Monad m => MonadSample m where
  sample : {name : AxisName} -> {i : Nat} -> (isSucc : IsSucc i) =>
    Dist name i -> m (Fin i)

||| Sampling as a costate on the container of distributions
public export
Sample : MonadSample m => {name : AxisName} -> {n : Nat} -> IsSucc n =>
  (m <!> Dist name n) =%> Scalar
Sample = toCostate sample
