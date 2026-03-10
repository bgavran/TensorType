module NN.Training.DataLoader

import Data.Vect

import Data.Container.Additive

import Control.Monad.Distribution
import Control.Monad.Sample.Definition
import Control.Monad.Sample.Instances


public export
record DataLoader (input : Type) (output : Type) where
  constructor MkDataLoader
  datasetSize : Nat
  dataset : Vect datasetSize (input, output)
  {auto isSucc : IsSucc datasetSize}

public export
inputs : DataLoader input output -> (n ** Vect n input)
inputs (MkDataLoader datasetSize dataset) = (datasetSize ** fst <$> dataset)

public export
makeDataLoader : Monad m => {datasetSize : Nat} -> IsSucc datasetSize =>
  (inputs : Vect datasetSize input) ->
  (groundTruthFn : input -> m output) ->
  m (DataLoader input output)
makeDataLoader xs groundTruthFn = do 
  ys <- traverse {f=m} {t=Vect datasetSize} groundTruthFn xs
  pure $ MkDataLoader datasetSize (zip xs ys)

||| Samples a single item from the dataset
public export
sample : DataLoader input output -> IO (input, output)
sample (MkDataLoader datasetSize dataset) = do
  n <- sample (uniform {i=datasetSize})
  pure (index n dataset)

public export
handleData : DataLoader x y ->
  Costate (IO <!> pushDown (x, y))
handleData dataLoader = toCostate $ \() => sample dataLoader <&> pure
