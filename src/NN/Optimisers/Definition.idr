module NN.Optimisers.Definition

import Data.Tensor
import Data.Container.Additive
import NN.Utils

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


-- todo upgrade to something like HasIO instead of IO?
public export
record Optimiser (paramCont : AddCont) (stateTy : Type) where
  constructor MkOptimiser
  ||| Notably, this is an ordinary dependent lens, not an additive one
  opt : (Const paramCont.Shp >< Const stateTy) =%> UC paramCont
  initParam : IO paramCont.Shp
  initState : IO stateTy

public export
(.fwd) : Optimiser p s -> (p.Shp, s) -> p.Shp
(.fwd) (MkOptimiser opt _ _) = opt.fwd

public export
(.bwd) : (opt : Optimiser pCont stateTy) ->
  (ps : (pCont.Shp, stateTy)) ->
  (pCont.Pos (opt.fwd ps)) ->
  (pCont.Shp, stateTy)
(.bwd) (MkOptimiser opt _ _) = opt.bwd

||| From 8.1.3. "Can we compose optimisers?" of https://arxiv.org/abs/2403.13001
||| Not used yet
public export
composeParallel : Optimiser pCont s ->
  Optimiser qCont t -> 
  Optimiser (pCont >< qCont) (s, t)
composeParallel (MkOptimiser o1 initP initS) (MkOptimiser o2 initQ initT) = MkOptimiser
  (!% \((p, q), (s, t)) => ((o1.fwd (p, s), o2.fwd (q, t)) **
    \(p', q') => let (pUpdated, sUpdated) = o1.bwd (p, s) p'
                     (qUpdated, tUpdated) = o2.bwd (q, t) q'
                 in ((pUpdated, qUpdated), (sUpdated, tUpdated))))
  (pairIO initP initQ)
  (pairIO initS initT)