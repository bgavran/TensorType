module NN.Utils

import Data.Nat
import Data.String
import Data.ScientificNotation
import Data.Materialise
import Misc

public export
runActionUntilMaxSteps : Materialise p =>
  ScientificDisplay p => ScientificDisplay l =>
  {default 100 printEvery : Nat} ->
  (action : p -> IO p) ->
  (maxSteps : Nat) ->
  (currentStep : Nat) -> (currentValue : p) ->
  (loss : p -> IO l) ->
  IO p
runActionUntilMaxSteps action maxSteps currStep currVal lossIO
  = go (minus maxSteps currStep) currStep currVal
  where
    stepWidth : Nat
    stepWidth = length (show maxSteps)

    rule : String
    rule = dim (String.replicate 50 '─')

    go : (remaining : Nat) -> (step : Nat) -> p -> IO p
    go 0 step val = do
      loss <- lossIO val
      putStrLn rule
      putStrLn "  Max steps (\{bold (show maxSteps)}) reached."
      putStrLn "  \{dim "Final loss:     "} \{yellow (showSci loss)}"
      putStrLn "  \{dim "Final params:   "} \{cyan (showSci val)}"
      putStrLn rule
      pure val
    go (S k) step val = do
      runIf (step `mod` printEvery == 0 || step < 10) $ do
        loss <- lossIO val
        putStrLn "  \{dim "step"} \{bold (padLeft stepWidth ' ' (show step))} \{dim "│ loss"} \{yellow (showSci loss)}"
      result <- action val
      -- we materialise the result between every training step
      go k (S step) (materialise result)
