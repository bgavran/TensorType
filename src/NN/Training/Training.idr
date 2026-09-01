module NN.Training.Training

import Data.Tensor
import Data.Container.Additive as Additive
import public Data.ScientificNotation
import NN.Optimisers

import NN.Utils
import NN.Training.DataLoader
import Data.Para
import Data.Autodiff.Model

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
||| `f : p -> l`, additionally handling some effect `e`
||| The optimiser used is allowed to be stateful meaning the result of the
||| optimisation is both the final parameter and the state of the optimiser
public export
optimiseStep : {p, l : AddCont} -> {e : Cont} ->
  InterfaceOnPositions l Num =>
  (f : p =%+> e >-+@ l) ->
  (handleEffect : Costate (IO <!> e)) ->
  (optimiser : Optimiser p stateTy) ->
  Costate (IO <!> (Const (p.Shp, stateTy)))
optimiseStep f handleEffect (MkOptimiser opt _) =
  let closeFunction : p =%+> !* e
      closeFunction = f %+>> (id >-+@ constantOne) %+>> actionToFree

      closeFunctionT : UC p =%> e -- transposed variant of closeFunction
      closeFunctionT = addContTransposeInv closeFunction

  in (IO <!> (opt %>> closeFunctionT)) %>> handleEffect

||| Evaluates the forward pass of some effectful lens
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
||| console.  Materialises parameter and state between steps
public export
optimise : {p, l : AddCont} -> {e : Cont} ->
  InterfaceOnPositions l Num =>
  {default 100 printEvery : Nat} ->
  Materialise p.Shp => Materialise stateTy =>
  ScientificDisplay p.Shp => ScientificDisplay l.Shp => ScientificDisplay stateTy =>
  (f : p =%+> e >-+@ l) ->
  (handleEffect : Costate (IO <!> e)) ->
  (initParam : IO p.Shp) ->
  (opt : Optimiser p stateTy) ->
  (numSteps : Nat) ->
  IO (p.Shp, stateTy)
optimise f handleEffect initParam opt numSteps = do
  currentValue <- initParam
  currentState <- opt.initState
  runActionUntilMaxSteps
    {l=l.Shp}
    {printEvery=printEvery}
    (fromCostate $ optimiseStep f handleEffect opt)
    numSteps
    0
    (currentValue, currentState)
    (fromCostate $ evalFw (f.fwd . opt.fwd) handleEffect)

||| TODO is the better name here "buildOptimiser"?
public export
buildSupervisedLearningSystem : (f : x =\\=> y) -> (loss : y =\\=> l) ->
  Materialise (Param f).Shp => InterfaceOnPositions (Param f) Materialise =>
  Param f =%+> (SupervisedData x.Shp (Param loss).Shp) >-+@ l
buildSupervisedLearningSystem f loss =
  let supplied : (a >*< b) >*< c =%+> a >*< (c >*< b)
      supplied = assocL %+>> (id >*< swap)
  in materialiseCont %+>> pushIntoContinuation {d=x>*<Param loss}
       (supplied %+>> (composePara f loss).Run)


namespace WithEffect
  ||| Evaluating the total loss over test/inference data in an effectul setting 
  ||| requires a handler for the effect. Usually when the effect is `Dist n`, 
  ||| the handler is simply sampling. We can't do anything else, really!
  public export
  totalLoss : Num l.Shp =>
    (f : x =\\=> e >-+@ y) ->
    (loss : y =\\=> l) ->
    (p : (Param f).Shp) ->
    (handleEffect : Costate (IO <!> e)) ->
    Costate (IO <!> (Const2 (Vect n (x.Shp, (Param loss).Shp)) l.Shp))
  totalLoss (MkPara pCont f) (MkPara z loss) p handleEffect
    = let evalFWithLoss : (x.Shp, z.Shp) -> IO l.Shp
          evalFWithLoss (x, yTrue) = do
            yPred <- fromCostate (evalFw f.fwd handleEffect) (x, p)
            pure $ loss.fwd (yPred, yTrue)
            -- putStrLn "Input: \{show x}, Predicted: \{show yPred}, Loss: \{show lossVal}"
      in toCostate $ \testData => do
        losses <- traverse evalFWithLoss testData
        pure $ Prelude.sum losses

  ||| Average loss in test/inference 
  public export
  averageLoss :  {n : Nat} ->
    Num l.Shp => Fractional l.Shp => Cast Nat l.Shp =>
    (f : x =\\=> e >-+@ y) ->
    (loss : y =\\=> l) ->
    (p : (Param f).Shp) ->
    (handleEffect : Costate (IO <!> e)) ->
    Costate (IO <!> (Const2 (Vect n (x.Shp, (Param loss).Shp)) l.Shp))
  averageLoss f loss p handleEffect = toCostate $ \testData => do
    lossSum <- fromCostate (totalLoss f loss p handleEffect) testData
    pure (lossSum / cast n)
  
namespace Model
  public export
  train : {a, b : AddCont} -> {l : AddCont} ->
    {default 100 printEvery : Nat} ->
    (m : a -\-> b) ->
    (loss : b =\\=> l) ->
    InterfaceOnPositions l Num =>
    ScientificDisplay l.Shp =>
    Materialise m.Params => Materialise stateTy =>
    ScientificDisplay m.Params => ScientificDisplay stateTy =>
    (trainData : DataLoader a.Shp (Param loss).Shp) ->
    (opt : Optimiser (ParamCont m) stateTy) ->
    (numSteps : Nat) ->
    IO (m.Params, stateTy)
  train m loss trainData opt numSteps = optimise {printEvery}
    (buildSupervisedLearningSystem (toPara m) loss)
    (handleData trainData)
    m.init
    opt
    numSteps

  ||| Average loss over a dataset
  public export
  averageLoss : {0 a, b, l : AddCont} ->
    (m : a -\-> b) ->
    (loss : b =\\=> l) ->
    Fractional l.Shp => Cast Nat l.Shp =>
    (p : m.Params) ->
    (dl : DataLoader a.Shp (Param loss).Shp) ->
    l.Shp
  averageLoss m (MkPara z loss) p dl =
    let pointLoss : (a.Shp, z.Shp) -> l.Shp
        pointLoss (x, yTrue) = loss.fwd (m.fwd x p, yTrue)
    in Prelude.sum (pointLoss <$> dl.dataset) / cast dl.datasetSize

  ||| Print a model's predictions on a dataset's inputs
  public export
  evalPrint : {0 a, b : AddCont} ->
    ScientificDisplay a.Shp => ScientificDisplay b.Shp =>
    (m : a -\-> b) -> (p : m.Params) ->
    DataLoader a.Shp b.Shp -> IO ()
  evalPrint m p dl = for_ dl.dataset $ \(x, _) =>
    putStrLn "Input: \{showSci x}, Predicted: \{showSci (m.fwd x p)}"


{-
-- todo write a variant of this with effects?
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