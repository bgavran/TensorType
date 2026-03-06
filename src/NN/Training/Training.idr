module NN.Training.Training

import Data.Tensor
import Data.Container.Additive as Additive
import NN.Optimisers.Definition
import NN.Optimisers.Instances
import NN.Utils
import Data.Para

{-------------------------------------------------------------------------------
{-------------------------------------------------------------------------------
todo will attempt to update this for monadic dependent lenses
This file defines functions which perform pure optimisation:
optimisation of a differentiable function `f : p -> x` (here modelled as a lens `f : p =%> x` via some optimiser such as gradient descent. 
Here no "loss function" or "input-output pairs" are needed, just a function to optimise.

This file provides functionality for creating, and turning supervised learning problems into pure optimisation problems, via a function which takes:
a) a parametric lens `f : x >< p =%>> y`
b) a loss function `loss : (y, y) =%> l`
c) input-output pairs `IO (x.Shp, y.Shp)`
and composes them to produce an optimisation problem `f : p =%> l` which the above described functions can consume.

Notably, only a *non-dependent* supervised-learning problem can be turned into a pure optimisation one. If the parameter space depends on the input, then learning becomes its own thing.


todo using Hom-version of optimisation becomes problematic if we either
a) have the dependency of the parameter on the input
b) use monadic lenses

-------------------------------------------------------------------------------}
-------------------------------------------------------------------------------}

||| Performs a single step of optimisation of some differentiable function
||| `f : p -> x`, where we additionally need to handle some effect `e`
||| Uses a potentially stateful optimiser, and returns an update of its
||| parameters and state
public export
optimiseStep : {p, l, e : AddCont} -> InterfaceOnPositions l Num =>
  (f : p =%> (e >@ l)) ->
  (handleEffect : Costate (IO <!> e)) ->
  (optimiser : Optimiser p stateTy) ->
  Costate (IO <!> (Const (p.Shp, stateTy)))
optimiseStep f handleEffect (MkOptimiser opt _ _) = 
  let handledEffect : p =%> e 
      handledEffect = f %>> (id >@ (constantOne {c=l})) %>> rightUnit
  in (IO <!> opt) %>> (IO <!> handledEffect) %>> handleEffect

public export
handleEffectLoss : {p, l, e : AddCont} -> InterfaceOnPositions l Num =>
  (f : p =%> (e >@ l)) ->
  (handleEffect : Costate (IO <!> e)) ->
  (optimiser : Optimiser p stateTy) ->
  Costate (IO <!> (Const2 (p.Shp, stateTy) l.Shp))
handleEffectLoss f handleEffect optimiser = toCostate $
  \(p, state) => do
  let (e <| lossGivenData) = f.fwd (optimiser.fwd (p, state))
  inputOutputPair <- fromCostate handleEffect e
  pure $ lossGivenData inputOutputPair

||| Performs function optimisation for `numSteps : Nat` times, while logging 
||| the progress to the console.
public export
optimise : {p, l, e : AddCont} -> InterfaceOnPositions l Num =>
  {default 100 printEvery : Nat} ->
  {default Nothing initParam : Maybe p.Shp} ->
  Show p.Shp => Show l.Shp => Show stateTy =>
  (f : p =%> e >@ l) ->
  (handleEffect : Costate (IO <!> e)) ->
  (opt : Optimiser p stateTy) ->
  (numSteps : Nat) ->
  IO (p.Shp, stateTy)
optimise f handleEffect opt numSteps = do
  currentValue : p.Shp <- case initParam of
    Just p => pure p
    Nothing => opt.initParam
  currentState <- opt.initState
  runActionUntilMaxSteps
    {l=l.Shp}
    {printEvery=printEvery}
    (fromCostate $ optimiseStep f handleEffect opt)
    numSteps
    0
    (currentValue, currentState)
    (fromCostate $ handleEffectLoss f handleEffect opt)

{-

||| todo we keep building the lens from scratch at every iteration
||| Given
||| a) a parametric lens `f : x >< p =%> y`
||| b) a loss function `loss : y >< y =%> l`
||| c) dataSampler `IO (x.Shp, y.Shp)`
||| builds a IO optimisation problem `IO (p =%> l)`
public export
buildSupervisedLearningSystem :
  {p, x, y, l, e : AddCont} ->
  (f : (x >< p) =%> y) ->
  (handleData : Costate (InputOutputData x y)) ->
  (loss : (y >< y) =%> l) ->
  Show x.Shp => Show y.Shp =>
  UC p =%> UC l
buildSupervisedLearningSystem f handleData loss =
  let withLoss : ((x >< p) >< y) =%> l
      withLoss = (f >< id) %>> (loss)

      rebracket : ((x >< y) >< p) =%> ((x >< p) >< y)
      rebracket = assocL %>> (id >< swap) %>> assocR
      
      stateXY : State (UC x >< UC y)
      stateXY = fromNapCostateToState {c=(UC x >< UC y)} handleData

      onlyP : UC p =%> ((UC x >< UC y) >< UC p)
      onlyP = leftUnitInv %>> (stateXY >< id)

      final : UC p =%> UC l
      final = onlyP %>> (ULens (rebracket %>> withLoss))

  in final
      --withLoss : ((x >< p) >< y) =%> (e >@ l)
      --withLoss = (f >< id) %>> rebracketcomptensor %>> (id >@ loss)
      -- withInputs = ((toState x >< id) >< toState yTrue) %>> withLoss
      -- pToELoss = leftUnitInv %>> rightUnitInv %>> withInputs
  -- putStrLn "Processing i(fnput-output pair: \{show x}, \{show yTrue}"

-}

public export
LabelledData : AddCont -> AddCont -> AddCont
LabelledData x y = !! (Const2 Unit (x.Shp, y.Shp))


-- public export
-- buildSupervisedLearningSystem :
--   {p, x, y, l, e : AddCont} ->
--   (f : (x >< p) =%> y) ->
--   (handleData : Costate (InputOutputData x y)) ->
--   (loss : (y >< y) =%> l) ->
--   Show x.Shp => Show y.Shp =>
--   UC p =%> UC l

public export
forwardWithLoss : Num l => (f : (x, p) -> y) ->
  (loss : (y, y) -> l) ->
  p ->
  List (x, y) ->
  l
forwardWithLoss f loss p xys =
  Prelude.sum $ (\(x, yTrue) => loss (f (x, p), yTrue)) <$> xys

public export
buildSupervisedLearningSystem : {x, y, p, l : AddCont} ->
  Num l.Shp =>
  (f : x >< p =%> y) ->
  (loss : (y >< y) =%> l) ->
  (p =%> (LabelledData x y) >@ l)
buildSupervisedLearningSystem f loss =
  let withLoss : ((x >< p) >< y) =%> l
      withLoss = (f >< id) %>> (loss)

      rebracket : ((x >< y) >< p) =%> ((x >< p) >< y)
      rebracket = assocL %>> (id >< swap) %>> assocR

      systemRebracketed : ((x >< y) >< p) =%> l
      systemRebracketed = rebracket %>> withLoss

  in ?hmmmm -- !%+ \p => (() <| forwardWithLoss f.fwd loss.fwd p **
     --  \ll => let lbwd = loss.bwd
     --             tt = (\(lio ** gradSum) => ?uhh) <$> ll
     --         in ?bw)

--   let withLoss : ((x >< p) >< y) =%> l
--       withLoss = (f >< id) %>> (loss)
-- 
--       rebracket : ((x >< y) >< p) =%> ((x >< p) >< y)
--       rebracket = assocL %>> (id >< swap) %>> assocR
--       
--       stateXY : State (UC x >< UC y)
--       stateXY = fromNapCostateToState {c=(UC x >< UC y)} handleData
-- 
--       onlyP : UC p =%> ((UC x >< UC y) >< UC p)
--       onlyP = leftUnitInv %>> (stateXY >< id)
-- 
--       final : UC p =%> UC l
--       final = onlyP %>> (ULens (rebracket %>> withLoss))

public export
train : {x, y, l : AddCont} -> InterfaceOnPositions l Num =>
  {default 100 printEvery : Nat} ->
  (f : ParaAddDLens x y) ->
  Show (GetParam f).Shp => Num l.Shp =>
  Show x.Shp => Show y.Shp => Show stateTy => Show l.Shp =>
  {default Nothing initParam : Maybe (GetParam f).Shp} ->
  (loss : (y >< y) =%> l) ->
  (dataSampler : Costate (IO <!> (LabelledData x y))) ->
  (opt : Optimiser (GetParam f) stateTy) ->
  (numSteps : Nat) ->
  IO ((GetParam f).Shp, stateTy)
train (MkPara p f) loss dataSampler = optimise
  {l=l}
  {e=LabelledData x y}
  {printEvery=printEvery}
  {initParam=initParam}
  (buildSupervisedLearningSystem f loss)
  dataSampler

{-

public export
totalLoss : {x, y : AddCont} ->
  (f : ParaAddDLens x y) ->
  (loss : (y >< y) =%> l) ->
  (p : (GetParam f).Shp) ->
  Show l.Shp => Num l.Shp =>
  (testData : Vect n (x.Shp, y.Shp)) ->
  IO l.Shp
totalLoss (MkPara pCont f) loss p [] = pure 0
totalLoss (MkPara pCont f) loss p ((x, yTrue) :: xs) = do
  let (yPred ** _) = (%!) f (x, p)
      (lossVal ** _) = (%!) loss (yPred, yTrue)
  lossRemaining <- totalLoss (MkPara pCont f) loss p xs
  pure (lossVal + lossRemaining)

public export
averageLoss : {x, y : AddCont} -> {n : Nat} ->
  (f : ParaAddDLens x y) ->
  (loss : (y >< y) =%> l) ->
  (p : (GetParam f).Shp) ->
  Show l.Shp => Num l.Shp => Fractional l.Shp =>
  Cast Nat l.Shp =>
  (testData : Vect n (x.Shp, y.Shp)) ->
  IO l.Shp
averageLoss f loss p testData = do
  totalLoss <- totalLoss f loss p testData
  pure (totalLoss / cast n)

public export
evalWithLoss : {x, y : AddCont} ->
  (f : ParaAddDLens x y) ->
  (loss : (y >< y) =%> l) ->
  (p : (GetParam f).Shp) ->
  Show x.Shp => Show y.Shp => Show l.Shp =>
  (testData : Vect n (x.Shp, y.Shp)) ->
  IO ()
evalWithLoss f loss p [] = pure ()
evalWithLoss (MkPara pCont f) loss p ((x, yTrue) :: xs) = do
  let (yPred ** _) = (%!) f (x, p)
      (lossVal ** _) = (%!) loss (yPred, yTrue)
  putStrLn "Input: \{show x}, Predicted: \{show yPred}, Loss: \{show lossVal}"
  evalWithLoss (MkPara pCont f) loss p xs

public export
eval : {x, y : AddCont} ->
  (f : ParaAddDLens x y) ->
  (p : (GetParam f).Shp) ->
  Show x.Shp => Show y.Shp =>
  (testData : Vect n x.Shp) ->
  IO ()
eval _ _ [] = pure ()
eval (MkPara pCont f) p (x :: xs) = do
  let (yPred ** _) = (%!) f (x, p)
  putStrLn "Input: \{show x}, Predicted: \{show yPred}"
  eval (MkPara pCont f) p xs


public export
debugPrint : {x, y : AddCont} ->
  Show x.Shp => Show y.Shp =>
  (name : String) ->
  (f : ParaAddMLens {m=IO} x y) ->
  Show (GetParam f).Shp =>
  ParaAddMLens {m=IO} x y
debugPrint name (MkPara pCont f) = MkPara
  pCont
  (!%%+ \(x, p) => do
    putStrLn "--------------------------------"
    putStrLn "\{name} input: \{show x}"
    putStrLn "\{name} parameter: \{show p}"
    (y ** ky) <- (%%!+ f) (x, p)
    putStrLn "\{name} output: \{show y}"
    putStrLn "--------------------------------"
    pure (y ** ky))
