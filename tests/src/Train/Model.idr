module Train.Model

import Hedgehog

import System.Random

import Data.Tensor
import Data.Container.Additive
import Data.Autodiff

||| Fixing init
affineM : Const Double -\-> Const Double
affineM = withInit scalarAffine (pure (0.5, 0.0))

testInp : Double
testInp = 3.0

testParam : (Double, Double)
testParam = (2.0, 1.0)

testGrad : Double
testGrad = 1.0


affineComp : Const Double -\-> Const Double
affineComp = affineM >>> affineM

testParam2 : (Double, Double)
testParam2 = (3.0, 0.0)

affineComp2 : Const Double -\-> (Const Double) >*< (Const Double)
affineComp2 = affineM &&& affineM

fanOut : (Double, Double)
fanOut = affineComp2.fwd 2.0 ((1.0, 0.0), (1.0, 0.0))

export
modelGroup : Group
modelGroup = MkGroup "Model tests"
    [ ("Baisc forward pass", property1 $ affineM.fwd testInp testParam === 7.0)
    , ("Basic backward pass (input and parameter gradients)", property1 $
        affineM.bwd testInp testParam testGrad === (2.0, (3.0, 1.0)))
    , ("Basic sequential", property1 $
        do affineComp.fwd 1.0 (testParam, testParam2) === 9.0
           affineComp.bwd 1.0 (testParam, testParam2) testGrad === (6.0, ((3.0, 3.0), (3.0, 1.0))))
    , ("Basic fan-out", property1 $ fanOut === (2.0, 2.0))
    ]
