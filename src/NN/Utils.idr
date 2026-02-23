module NN.Utils

import Data.Nat
import Misc

public export
runActionUntilMaxSteps : Show p => Show l =>
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
        putStrLn "Current step: \{show currStep}, loss: \{show (loss)}"
        -- putStrLn "Current step: \{show currStep}, value: \{show currVal}, loss: \{show (loss)}"
      result <- action currVal
      runActionUntilMaxSteps {printEvery=printEvery} action maxSteps (currStep + 1) result lossIO
    False => do
      loss <- lossIO currVal
      -- putStrLn "Max steps (\{show maxSteps}) reached. Final loss: \{show (loss)}"
      putStrLn "--------------------------------------------------"
      putStrLn "Max steps (\{show maxSteps}) reached. Final loss: \{show (loss)}."
      putStrLn "Final parameter values: \{show currVal}."
      putStrLn "--------------------------------------------------"
      pure currVal
