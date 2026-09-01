module Train.TensorPrimitives

import Hedgehog

import System.Random

import Data.Tensor
import Data.Container.Additive
import Data.Autodiff
import NN.Architectures.Affine

X : Axis
X = "x" ~~> 2

Y : Axis
Y = "y" ~~> 2

aff : Const (Tensor [X] Double) -\-> Const (Tensor [Y] Double)
aff = affineModel

input : Tensor [X] Double
input = ># [1, 1]

params : AffineParams X Y Double
params = (># [ [1, 2]
             , [3, 4] ], ># [10, 20])

||| To avoid recomputing
affFwd : Tensor [Y] Double
affFwd = aff.fwd input params

||| To avoid recomputing
affBwd : (Tensor [X] Double, AffineParams X Y Double)
affBwd = aff.bwd input params (># [1, 0])

rel : Const (Tensor [X] Double) -\-> Const (Tensor [X] Double)
rel = reluModel

reluIn : Tensor [X] Double
reluIn = ># [2, -3]

reluBwd : Tensor [X] Double
reluBwd = fst (rel.bwd reluIn () (># [1, 1]))

export
tensorPrimitivesGroup : Group
tensorPrimitivesGroup = MkGroup "Tensor primitives (Model)"
    [ ("affine forward", property1 $ affFwd === ># [13, 27])
    , ("affine input gradient", property1 $ fst affBwd === ># [1, 2])
    , ("affine weight gradient", property1 $
        fst (snd affBwd) === ># [ [1, 1]
                                , [0, 0] ])
    , ("affine bias gradient", property1 $ snd (snd affBwd) === ># [1, 0])
    , ("relu forward passes positives, kills negatives", property1 $ 
      rel.fwd reluIn () === ># [2, 0])
    , ("relu gradient gates on the sign of the input", property1 $
      fst (rel.bwd reluIn () (># [1, 1])) === ># [1, 0])
    ]
