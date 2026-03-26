module Control.Monad.Sample.Definition

import Data.Fin

import Control.Monad.Distribution

||| Interface for sampling from a distribution
||| We require that there is at least one element in the distribution
||| TODO add temperature as a implicit parameter with a defualt value of 1.0
public export
interface Monad m => MonadSample m where
  sample : {i : Nat} -> (isSucc : IsSucc i) =>
    Dist i -> m (Fin i)