module NN.Training.Training

import Data.Tensor
import Data.Container.Additive as Additive
import NN.Optimisers.Definition
import NN.Optimisers.Instances
import NN.Architectures.LossFunctions

import NN.Utils
import Data.Para

{-------------------------------------------------------------------------------
{-------------------------------------------------------------------------------
TODO update this in light of effects

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
  let closeFunction : p =%> e 
      closeFunction = f %>> (id >@ constantOne) %>> rightUnit
  in (IO <!> opt) %>> (IO <!> closeFunction) %>> handleEffect

||| Evaluates a the forward pass of some effectful lens
public export
evalFw : {0 e : Cont} ->
  (f : a -> Ext e b) ->
  (handleEffect : Costate (IO <!> e)) ->
  Costate (IO <!> (Const2 a b))
evalFw f handleEffect = toCostate $ \ps => do
  let (eInp <| outGivenEffect) = f ps 
  e <- fromCostate handleEffect eInp
  pure $ outGivenEffect e

||| Iterates `optimiseStep` `numSteps` times, and logs the progress to the 
||| console
public export
optimise : {p, l, e : AddCont} -> InterfaceOnPositions l Num =>
  {default 100 printEvery : Nat} ->
  {default Nothing customInitParam : Maybe p.Shp} ->
  Show p.Shp => Show l.Shp => Show stateTy =>
  (f : p =%> e >@ l) ->
  (handleEffect : Costate (IO <!> e)) ->
  (opt : Optimiser p stateTy) ->
  (numSteps : Nat) ->
  IO (p.Shp, stateTy)
optimise f handleEffect opt numSteps = do
  currentValue : p.Shp <- case customInitParam of
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
    (fromCostate $ evalFw (f.fwd . opt.fwd) handleEffect)

||| Given
||| a) a parametric lens `f : x >< p =%> y`
||| b) a loss function `loss : y >< y =%> l`
||| builds an effectful lens `p =%> l`
public export
buildSupervisedLearningSystem : Num l.Shp => IsFlat l =>
  (f : ParaAddDLens x y) ->
  (loss : Loss y {l=l}) ->
  ((GetParam f) =%> (pushDown (x >< y)) >@ l)
buildSupervisedLearningSystem (MkPara p f) loss =
  let rebracket : ((x >< y) >< p) =%> ((x >< p) >< y)
      rebracket = assocL %>> (id >< swap) %>> assocR
  in pushIntoContinuation {d=x><y} (rebracket %>> (f >< id) %>> loss)


namespace WithEffect
  ||| When it comes to effects which involve sampling, where the 'correct' answer
  ||| is stored in the test data, there are different ways of evaluating the loss
  ||| One is to use that correct label to force the correct branch to run, but
  ||| that is impossible with the current type signature
  ||| Instead, we opt out for the more accurate method of sampling during loss
  ||| evaluation
  public export
  totalLoss : Show l.Shp => Num l.Shp =>
    (f : ParaAddDLens x (e >@ y)) ->
    (loss : Loss y {l=l}) ->
    (p : (GetParam f).Shp) ->
    (handleEffect : Costate (IO <!> e)) ->
    Costate (IO <!> (Const2 (Vect n (x.Shp, y.Shp)) l.Shp))
  totalLoss (MkPara pCont f) loss p handleEffect = toCostate $ \testData => do
    let evalFWithLoss : (x.Shp, y.Shp) -> IO l.Shp
        evalFWithLoss (x, yTrue) = do
          yPred <- fromCostate (evalFw f.fwd handleEffect) (x, p)
          pure $ loss.fwd (yPred, yTrue)
          -- putStrLn "Input: \{show x}, Predicted: \{show yPred}, Loss: \{show lossVal}"
    losses <- traverse evalFWithLoss testData
    pure $ Prelude.sum losses
  
  public export
  averageLoss :  {n : Nat} ->
    Show l.Shp => Num l.Shp => Fractional l.Shp => Cast Nat l.Shp =>
    (f : ParaAddDLens x (e >@ y)) ->
    (loss : Loss y {l=l}) ->
    (p : (GetParam f).Shp) ->
    (handleEffect : Costate (IO <!> e)) ->
    Costate (IO <!> (Const2 (Vect n (x.Shp, y.Shp)) l.Shp))
  averageLoss f loss p handleEffect = toCostate $ \testData => do
    lossSum <- fromCostate (totalLoss f loss p handleEffect) testData
    pure (lossSum / cast n)
  
  ||| Eval a model and loss with specific parameters, in the presence of an effect
  public export
  evalWithLoss : Show x.Shp => Show y.Shp => Show l.Shp =>
    (f : ParaAddDLens x (e >@ y)) ->
    (loss : Loss y {l=l}) ->
    (p : (GetParam f).Shp) ->
    (handleEffect : Costate (IO <!> e)) ->
    Costate (IO <!> (Const2 (Vect n (x.Shp, y.Shp)) Unit))
  evalWithLoss (MkPara pCont f) loss p handleEffect = toCostate $ \testData => do 
    let evalFWithLoss : (x.Shp, y.Shp) -> IO ()
        evalFWithLoss (x, yTrue) = do
          yPred <- fromCostate (evalFw f.fwd handleEffect) (x, p)
          let lossVal = loss.fwd (yPred, yTrue)
          putStrLn "Input: \{show x}, Predicted: \{show yPred}, Loss: \{show lossVal}"
    _ <- traverse evalFWithLoss testData
    pure ()
  
  ||| Eval a model with specific parameters, in the presence of an effect
  public export
  eval : Show x.Shp => Show y.Shp =>
    (f : ParaAddDLens x (e >@ y)) ->
    (p : (GetParam f).Shp) ->
    (handleEffect : Costate (IO <!> e)) ->
    Costate (IO <!> (Const2 (Vect n x.Shp) Unit))
  eval (MkPara _ f) p handleEffect = toCostate $ \testData => do
    let evalF : x.Shp -> IO ()
        evalF x = do
          yPred <- fromCostate (evalFw f.fwd handleEffect) (x, p)
          putStrLn "Input: \{show x}, Predicted: \{show yPred}"
    _ <- traverse evalF testData
    pure ()

namespace WithoutEffect
  public export
  trivialEffect : {y : AddCont} ->
    ParaAddDLens x y -> ParaAddDLens x (Scalar >@ y)
  trivialEffect (MkPara p f) = MkPara p
    (f %>> leftUnitInv)

  public export
  handleTrivial : Costate (IO <!> Additive.Object.Instances.Scalar)
  handleTrivial = toCostate $ \() => pure ()


  public export
  eval : {y : AddCont} -> Show x.Shp => Show y.Shp =>
    (f : ParaAddDLens x y) ->
    (p : (GetParam f).Shp) ->
    Costate (IO <!> (Const2 (Vect n x.Shp) Unit))
  eval (MkPara pCont f) p
    = eval {e=Scalar} (MkPara pCont (f %>> leftUnitInv)) p handleTrivial

  public export
  averageLoss :  {y : AddCont} -> {n : Nat} ->
    Show l.Shp => Num l.Shp => Fractional l.Shp => Cast Nat l.Shp =>
    (f : ParaAddDLens x y) ->
    (loss : Loss y {l=l}) ->
    (p : (GetParam f).Shp) ->
    Costate (IO <!> (Const2 (Vect n (x.Shp, y.Shp)) l.Shp))
  averageLoss (MkPara pCont f) loss p = averageLoss {e=Scalar}
    (MkPara pCont (f %>> leftUnitInv))
    loss
    p
    handleTrivial
  

{-
public export
train : {x, y, l : AddCont} -> InterfaceOnPositions l Num => IsFlat l =>
  {default 100 printEvery : Nat} ->
  (f : ParaAddDLens x y) ->
  Show (GetParam f).Shp => Num l.Shp =>
  Show x.Shp => Show y.Shp => Show stateTy => Show l.Shp =>
  {default Nothing initParam : Maybe (GetParam f).Shp} ->
  (loss : (y >< y) =%> l) ->
  (handleData : Costate (IO <!> (pushDown (x >< y)))) ->
  (opt : Optimiser (GetParam f) stateTy) ->
  (numSteps : Nat) ->
  IO ((GetParam f).Shp, stateTy)
train f loss handleData = optimise
  {e=pushDown (x><y)}
  {printEvery=printEvery}
  {initParam=initParam}
  (buildSupervisedLearningSystem f loss)
  handleData
-}

{-
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

-- namespace Additive
--   ||| Evaluates a the forward pass of some effectful lens
--   public export
--   evalFw : {0 a, e, b : AddCont} ->
--     (f : a =%> (e >@ b)) ->
--     (handleEffect : Costate (IO <!> e)) ->
--     Costate (IO <!> (Const2 a.Shp b.Shp))
--   evalFw f handleEffect = toCostate $ \ps => do
--     let (eInp <| outGivenEffect) = f.fwd ps 
--     e <- fromCostate handleEffect eInp
--     pure $ outGivenEffect e
