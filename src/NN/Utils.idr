module NN.Utils

import Data.Nat
import Data.String
import Data.ScientificNotation
import Data.Materialise
import Misc

public export
runActionUntilMaxSteps : Materialise p =>
  ScientificDisplay p =>
  ScientificDisplay l =>
  {default 100 printEvery : Nat} ->
  (action : p -> IO p) ->
  (maxSteps : Nat) ->
  (currentStep : Nat) -> (currentValue : p) ->
  (loss : p -> IO l) ->
  IO p
runActionUntilMaxSteps action maxSteps currStep currVal lossIO
  = case currStep < maxSteps of
    True => do
      runIf (currStep `mod` printEvery == 0 || currStep < 10) $ do
        loss <- lossIO currVal
        putStrLn "  \{dim "step"} \{bold (padLeft stepWidth ' ' (show currStep))} \{dim "│ loss"} \{yellow (showSci loss)}"
      result <- action currVal
      -- we materialise the result between every training step
      runActionUntilMaxSteps {printEvery=printEvery} action maxSteps (assert_smaller currStep (currStep + 1)) (materialise result) lossIO
    False => do
      loss <- lossIO currVal
      putStrLn rule
      putStrLn "  Max steps (\{bold (show maxSteps)}) reached."
      putStrLn "  \{dim "Final loss:     "} \{yellow (showSci loss)}"
      putStrLn "  \{dim "Final params:   "} \{cyan (showSci currVal)}"
      putStrLn rule
      pure currVal
  where
    stepWidth : Nat
    stepWidth = length (show maxSteps)

    rule : String
    rule = dim (String.replicate 50 '─')
