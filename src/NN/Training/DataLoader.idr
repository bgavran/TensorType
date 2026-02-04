module NN.Training.DataLoader

import Data.Vect

import Control.Monad.Distribution
import Control.Monad.Sample


public export
record DataLoader (input : Type) (output : Type) where
  constructor MkDataLoader
  datasetSize : Nat
  dataset : Vect datasetSize (input, output)
  {auto isSucc : IsSucc datasetSize}



public export
sample : DataLoader input output -> IO (input, output)
sample (MkDataLoader datasetSize dataset) = do
  n <- sample (uniform {i=datasetSize})
  pure (index n dataset)
