module NN.Optimisers.Definition

import Data.Tensor
import Data.Autodiff.AdditiveContainer

||| Stateful optimiser
||| Because we use dependent Para, optimiser parameter can depend on input
public export
record Optimiser {inputTy : Type}
  (paramCont : inputTy -> AddCont)
  (stateTy : Type) -- 
  where
  constructor MkOptimiser
  opt : (x : inputTy) ->
    (Const (paramCont x).Shp >< Const stateTy) =%> UC (paramCont x)