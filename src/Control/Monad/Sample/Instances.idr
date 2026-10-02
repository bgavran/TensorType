module Control.Monad.Sample.Instances

import Control.Monad.Identity
import System.Random

import Data.Tensor
import Control.Monad.Distribution
import Control.Monad.Sample.Definition

||| Max sampler, always picks the element with the highest logit
public export
[pickMax] Monad m => MonadSample m where
  sample = toCostate $ \d => pure (argmax d.logits)

||| Min sampler, always picks the element with the lowest logit
public export
[pickMin] Monad m => MonadSample m where
  sample = toCostate $ \d => pure (argmin d.logits)

||| Sample an index of a cubical distribution
||| Compute the cumulative distribution, draw uniformly, find the right bin 
public export
sampleCubical : {n : Nat} -> {name : AxisName} ->
  Tensor [name ~~> n] Double -> IO (Maybe (Fin n))
sampleCubical {n = Z} _ = pure Nothing
sampleCubical {n = S k} logits = do
  let cumSum = Utils.cumulativeSum (softargmaxImpl logits)
  r <- randomRIO (0.0, 1.0)
  pure $ findBin (#> cumSum) r

||| Flattens a container distribution, sample the cubicla, map the index back
public export
MonadSample IO where
  sample @{ne} @{MkIsFoldable toL} = toCostate $ \d => do
    Just k <- sampleCubical (flatten toL d.logits)
      | Nothing => pure (GetInterface ne d.logits.extractShapeRank1) -- should never happen
    pure (toL.bwd d.logits.extractShapeRank1 k)
