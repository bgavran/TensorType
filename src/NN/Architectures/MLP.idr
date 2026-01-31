module NN.Architectures.MLP

import Data.Tensor
import Data.Para

import NN.Architectures.Affine
import NN.Architectures.Activations


||| N-layer multi-layer perceptron with a specified activation function,
||| and flag for whether the last layer should have it
public export
multiLayerPerceptron : {a : Type} -> Num a =>
  {ieva : Cont} ->
  (allAlg : AllAlgebra [ieva] a) =>
  (allAppl : TensorMonoid ieva) =>
  (numLayers : Nat) ->
  (activation : CTensor [ieva] a -\-> CTensor [ieva] a) ->
  {default False lastLayerActivation : Bool} ->
  CTensor [ieva] a -\-> CTensor [ieva] a
multiLayerPerceptron 0 _ = id
multiLayerPerceptron 1 activation {lastLayerActivation = False}
  = affinePara
multiLayerPerceptron 1 activation {lastLayerActivation = True}
  = composePara affinePara activation
multiLayerPerceptron (S (S k)) activation
  = composePara (composePara affinePara activation) (multiLayerPerceptron (S k) activation {lastLayerActivation = lastLayerActivation})







public export
threeLayerPerceptron : {inputSize, outputSize : Nat} ->
  Tensor [inputSize] Double -\-> Tensor [outputSize] Double
threeLayerPerceptron =
  let hiddenDimension1 = inputSize * 10
      hiddenDimension2 = inputSize * 10
  in     affinePara
     \>> trivialParam Tensor.sigmoid
     \>> affinePara {x=Vect hiddenDimension1}
     \>> trivialParam Tensor.sigmoid
     \>> affinePara {x=Vect hiddenDimension2}





-- public export
-- inputTensor : Tensor [3] Double
-- inputTensor = ># [1, 2, 3]
-- 
-- 
-- public export
-- outputTensor : IO (Tensor [2] Double)
-- outputTensor = do
--   let pr = randomRIO {io=IO} {a=(Param (trivialParam Tensor.sigmoid) inputTensor)}
--   ?asdfasdf

  {-
public export
mlpNonDependentPara : {a : Type} -> Num a =>
  {ieva : Cont} ->
  (allAlg : AllAlgebra [ieva] a) =>
  (allAppl : All TensorMonoid [ieva]) =>
  (numLayers : Nat) ->
  (activation : CTensor [ieva] a -> CTensor [ieva] a) ->
  {default False lastLayerActivation : Bool} ->
  IsNotDependent (multiLayerPerceptron numLayers (trivialParam activation) {lastLayerActivation = lastLayerActivation})
mlpNonDependentPara 0 activation = ?oqwi -- MkNonDep () (\t, _ => t)
mlpNonDependentPara 1 activation {lastLayerActivation = False}
  = MkNonDep (AffineLayerParams ieva ieva a)
    (\x, p => (Run (multiLayerPerceptron 1 (trivialParam activation) {lastLayerActivation = False})) x p)
mlpNonDependentPara 1 activation {lastLayerActivation = True} = ?wiii_1 -- MkNonDep ?ppp ?fff
mlpNonDependentPara (S k) activation = ?wiii_11 -- MkNonDep ?ppp ?fff
  -- = MkNonDep ?ppp ?fff



public export
simpleNLayerNet : {features : Nat} -> (n : Nat) ->
  Tensor [features] Double -\-> Tensor [features] Double
simpleNLayerNet n = multiLayerPerceptron n (trivialParam sigmoid)


public export
exampleInput : Tensor [2] Double
exampleInput = ># [1, 5]

public export
exampleParam : Tensor [2, 2] Double
exampleParam = ># [ [0.4, 0.2]
                  , [0.7, -3]]

public export
exampleBias : Tensor [2] Double
exampleBias = ># [0, 0]

public export
layerParam : AffineLayerParams (Vect 2) (Vect 2) Double
layerParam = MkParams exampleParam exampleBias

public export
exampleOutput : Tensor [2] Double
exampleOutput = Run (simpleNLayerNet 2) exampleInput
  ((layerParam ** ()) ** layerParam)
