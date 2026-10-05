module NN.Training.DataLoader

import Data.Tensor
import Data.Container.Additive

import Control.Monad.Distribution
import Control.Monad.Sample.Definition
import Control.Monad.Sample.Instances

public export
DatasetAxis : Axis
DatasetAxis = "dataset" ~> List1

||| A container whose shapes are tensors over a List1 container, and 
||| positions are specific choices of input-output pairs
||| TODO Does any other container other than `List1` make sense?
public export
DataLoader : (input, output : Type) -> Cont
DataLoader input output = Pick [DatasetAxis] (input, output)

public export
Dataset : (input, output : Type) -> Type
Dataset input output = (DataLoader input output).Shp

||| The number of entries, one more than the shape of `List1`
public export
datasetSize : Dataset input output -> Nat
datasetSize dl = S dl.extractShapeRank1

||| On the forward pass: given a dataset, get its size, and produce a uniform 
||| distribution over that many elements.
||| On the bw pass: given the index in that size, pick the actual element 
||| corresponding to it
public export
dataLens : DataLoader input output =%> Dist DatasetAxis
dataLens = Tensor.pick %>> rightUnit %>> uniformLens

||| Handler for the dataset, samples from it uniformly
public export
handleData : Costate (IO <!> DataLoader input output)
handleData = (IO <!> dataLens) %>> sample

||| The container used to store data for a supervised learning system
||| Single shape, positions are (input, output) pairs
public export
SupervisedData : (input, output : Type) -> Cont
SupervisedData input output = Nap (input, output)

||| Sampling from one particular dataset
public export
handleDataFor : (dl : Dataset x y) -> Costate (IO <!> SupervisedData x y)
handleDataFor dl = (IO <!> atShape {c = DataLoader x y} dl) %>> handleData

||| A dataset from a batch of inputs and a ground-truth function
public export
makeDataLoader : Monad m =>
  {batch : Axis} -> (isCub : IsCubical batch) => IsSucc (batch.dim) =>
  (xs : Tensor [batch] input) ->
  (groundTruthFn : input -> m output) ->
  m (Dataset input output)
makeDataLoader {isCub = MkIsCubical _ (S k)} xs groundTruthFn
  = restructureAxis vectToList1 . liftA2Tensor xs <$> traverse groundTruthFn xs