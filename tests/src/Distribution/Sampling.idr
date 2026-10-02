module Distribution.Sampling

import Hedgehog

import System.Random

import Data.Tensor
import Control.Monad.Distribution
import Control.Monad.Sample.Definition
import Control.Monad.Sample.Instances
import Control.Monad.Identity
import Data.Fin

Coin : Axis
Coin = "coin" ~~> 2

TenChoices : Axis
TenChoices = "ten" ~~> 10

||| Distribution ~[0.1, 0.9] in logit form
coinDist : Dist Coin
coinDist = MkDist (># [-1.099, 1.099]) 

||| Dirac delta on 10 choices, parameterised
diracFromTen : Fin 10 -> Dist TenChoices
diracFromTen i = diracDelta {a=TenChoices} i

export
samplingGroup : Group
samplingGroup = MkGroup "Sampling"
  [ ("Sampling a Dirac delta with pickMax returns the index", property1 $
      runIdentity (fromCostate (sample @{pickMax}) (diracFromTen 2)) === 2)
  ]

export
samplingIOGroup : IO Group
samplingIOGroup = do
  srand 42
  hundredCoinTosses <- sequence (replicate 100 (fromCostate sample coinDist))
  hundredDiracDraws <- sequence (replicate 100 (fromCostate sample (diracFromTen 4)))
  pure $ MkGroup "Sampling (random)"
    [ ("A [0.1, 0.9] coin gives 1 about 90 times in 100", property1 $ do
        let ones = count (== 1) hundredCoinTosses
        diff ones (>=) 80
        diff ones (<=) 98)
    , ("Sampling a Dirac delta always returns its index", property1 $
        count (== 4) hundredDiracDraws === 100)
    ]
