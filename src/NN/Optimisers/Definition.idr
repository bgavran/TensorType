module NN.Optimisers.Definition

import Data.Tensor
import Data.Container.Additive

-- We can make a choice in optimisation:
-- a) either the parameter can depend on the input, in which case we can't use the hom representation of a learner
-- b) or it doesn't, meaning we can curry the learner and treat it as something we optimise


||| Dependent stateful optimiser, modelled as a dependent lens
||| Dependent version of section 8.1.3 of https://arxiv.org/abs/2403.13001
||| Because we use dependent Para, optimiser can depend on the input
public export
record DOptimiser {inputTy : Type}
  (paramCont : inputTy -> AddCont)
  (stateTy : Type)
  where
  constructor MkDOptimiser
  ||| Notably this produces an ordinary dependent lens, not an additive one
  opt : (x : inputTy) ->
    (Const (paramCont x).Shp >< Const stateTy) =%> UC (paramCont x)


public export
record Optimiser (paramCont : AddCont) (stateTy : Type) where
  constructor MkOptimiser
  ||| Notably, this is an ordinary dependent lens, not an additive one
  opt : (Const paramCont.Shp >< Const stateTy) =%> UC paramCont