module Control.Monad.Sample.Definition

import Data.Fin

import Data.Container.Base
import Data.Tensor
import Control.Monad.Distribution

||| Interface for sampling from a distribution
||| Sampling is a costate/server for distributions
||| We require that there is at least one element in the distribution
||| We also require that we can fold over the elements, i.e. that positions 
||| are finite and have an order
||| TODO add temperature as a implicit parameter with a default value of 1.0
public export
interface Monad m => MonadSample m where
  sample : {a : Axis} ->
    (isNonEmpt : IsNonEmpty a.cont) =>
    (isFoldable : IsFoldable a.cont) =>
    Costate (m <!> Dist a)