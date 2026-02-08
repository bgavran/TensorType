module NN.Utils

import Data.Nat

public export
runIf: Bool -> IO () -> IO ()
runIf True action = action
runIf False action = pure ()

public export
pairIO : IO a -> IO b -> IO (a, b)
pairIO a b = do
  a <- a
  b <- b
  pure (a, b)

public export
runActionUntilMaxSteps : Show p => Show l =>
  (action : p -> IO p) ->
  (maxSteps : Nat) ->
  (currentStep : Nat) -> (currentValue : p) ->
  (loss : IO (p -> l)) ->
  IO p
runActionUntilMaxSteps action maxSteps currStep currVal lossIO
  = case currStep < maxSteps of
    True => do
      runIf (currStep `mod` 100 == 0) $ do
        loss <- lossIO
        putStrLn "Current step: \{show currStep}, value: \{show currVal}, loss: \{show (loss currVal)}"
      result <- action currVal
      runActionUntilMaxSteps action maxSteps (currStep + 1) result lossIO
    False => do
      loss <- lossIO
      putStrLn "Max steps (\{show maxSteps}) reached. Final value: \{show currVal}. Final loss: \{show (loss currVal)}"
      pure currVal
