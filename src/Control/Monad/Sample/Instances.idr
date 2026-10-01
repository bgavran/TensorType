module Control.Monad.Sample.Instances

import Control.Monad.Identity
import System.Random

import Data.Tensor
import Control.Monad.Distribution
import Control.Monad.Sample.Definition

||| Max sampler, always picks the element with the highest logit
public export
[pickMax] MonadSample Identity where
  sample = toCostate $ \d => Id (argmax d.logits)

||| Min sampler, always picks the element with the lowest logit
public export
[pickMin] MonadSample Identity where
  sample = toCostate $ \d => Id (argmin d.logits)

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

{-
-- todo move to tests
testIO : IO ()
testIO = do
  let logits : Dist "coin" 2
      logits = MkDist (># [-(1.099), 1.099]) -- this produces the dist [0.1, 0.9]
  is <- sequence (replicate 1000 ((fromCostate sample) logits))
  -- printLn is
  printLn (count (== 0) is) -- should be ~100
  printLn (count (== 1) is) -- should be ~900

public export
testDirac : IO ()
testDirac = do
  let index = 4
  let logits = diracDelta {name="dirac"} {i=10} index
  inds <- sequence (replicate 1000 ((fromCostate sample) logits))
  printLn (take 10 inds)
  printLn (count (== index) inds)
