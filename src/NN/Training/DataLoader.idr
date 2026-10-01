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
||| TODO Does any other container other than `List1`make sense?
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

||| A batch is a dataset: the batch axis forgets its size and takes the
||| dataset's name
public export
fromBatch : {batch : Axis} -> (c : IsCubical batch) => IsSucc (batch.dim) =>
  Tensor [batch] a -> Tensor [DatasetAxis] a
fromBatch {c = MkIsCubical _ (S k)} = restructureAxis vectToList1

||| A dataset from a batch of inputs and a ground-truth function
public export
makeDataLoader : Monad m =>
  {batch : Axis} -> (c : IsCubical batch) => IsSucc (batch.dim) =>
  (inputs : Tensor [batch] input) ->
  (groundTruthFn : input -> m output) ->
  m (Dataset input output)
makeDataLoader {c = MkIsCubical _ (S k)} xs groundTruthFn
  = fromBatch . liftA2Tensor xs <$> traverse groundTruthFn xs

||| A dataset from a batched input tensor and a ground-truth function;
||| the label type stays generic (it need not be a tensor)
public export
fromBatchedTensor : Monad m =>
  {batch : Axis} -> (c : IsCubical batch) => IsSucc (batch.dim) =>
  {0 shape : TensorShape rank} ->
  (0 _ : batch `ConsistentWith` shape) =>
  (xs : Tensor (batch :: shape) a) ->
  (groundTruthFn : Tensor shape a -> m output) ->
  m (Dataset (Tensor shape a) output)
fromBatchedTensor xs = makeDataLoader (toNestedTensor xs)

||| A dataset from batched input and label tensors: tensor labels as the default
public export
fromBatchedTensors : {batch : Axis} -> (c : IsCubical batch) => IsSucc (batch.dim) =>
  {0 sx, sy : TensorShape rank} ->
  (0 _ : batch `ConsistentWith` sx) => (0 _ : batch `ConsistentWith` sy) =>
  (xs : Tensor (batch :: sx) a) ->
  (ys : Tensor (batch :: sy) b) ->
  Dataset (Tensor sx a) (Tensor sy b)
fromBatchedTensors {c = MkIsCubical _ (S k)} xs ys
  = fromBatch (liftA2Tensor (toNestedTensor xs) (toNestedTensor ys))
