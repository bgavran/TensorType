module Control.Monad.Sample

import System.Random

import Data.Container
import Data.Tensor 

import Control.Monad.Distribution
import Control.Monad.Identity
import NN.Architectures.Softargmax

import Misc

||| Interface for sampling from a distribution
||| We require that there is at least one element in the distribution
||| TODO add temperature as a implicit parameter with a defualt value of 1.0
public export
interface Monad m => MonadSample m where
  sample : {i : Nat} -> (isSucc : IsSucc i) =>
    Dist i -> m (Fin i)


||| Trivial sampler, always picks the first element
public export
[pickFirst] MonadSample Identity where
  sample {i = (S k)} (MkDist xs) = Id FZ

||| Max sampler, always picks the element with the highest logit
public export
[pickMax] MonadSample Identity where
  sample {i = (S k)} (MkDist xs) = Id (argmax xs)

||| Min sampler, always picks the element with the lowest logit
public export
[pickMin] MonadSample Identity where
  sample {i = (S k)} (MkDist xs) = Id (argmin xs)


||| Computes the cumulative distribution, samples randomly, finds the right bin
public export
MonadSample IO where
  sample @{ItIsSucc} (MkDist xs) = do
    let dist : Tensor [i] Double := (softargmaxImpl {i=(Vect i)}) (># xs)
        cumSum : Tensor [i] Double := cumulativeSum dist
    r <- randomRIO (0.0, 1.0)
    case findBin (#> cumSum) r of
      Nothing => pure FZ -- should never happen!
      Just i => pure i



testIO : IO ()
testIO = do
  let logits = MkDist [-(1.099), 1.099] -- this produes the dist [0.1, 0.9]
  is <- sequence (replicate 1000 (sample logits))
  -- printLn is
  printLn (count (== 0) is) -- should be ~100
  printLn (count (== 1) is) -- should be ~900
