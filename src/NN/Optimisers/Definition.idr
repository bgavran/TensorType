module NN.Optimisers.Definition

import Data.Tensor
import Data.Autodiff.AdditiveContainer

||| Stateful optimiser, modelled as a dependent lens
||| As described in section 8.1.3 of https://arxiv.org/abs/2403.13001
||| Because we use dependent Para, optimiser can depend on the input
public export
record Optimiser {inputTy : Type}
  (paramCont : inputTy -> AddCont)
  (stateTy : Type)
  where
  constructor MkOptimiser
  opt : (x : inputTy) ->
    (Const (paramCont x).Shp >< Const stateTy) =%> UC (paramCont x)