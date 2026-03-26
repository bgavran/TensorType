module NN.Optimisers.Instances

import System.Random

import Data.Container.Additive
import Data.Num
import NN.Optimisers.Definition
import NN.Utils

||| Gradient descent optimiser. Has trivial state
||| @lr is the learning rate
public export
GD : Num pType => Neg pType => Random pType =>
  (mon : ComMonoid pType) => FromDouble pType =>
  {default 0.001 lr : pType} -> Optimiser (Const pType) Unit
GD = MkOptimiser
  (!% \(p, ()) => (p ** \p' => (p - lr * p', ())))
  (randomRIO (-1, 1))
  (pure ())

||| Gradient ascent optimiser. Has trivial state
||| @lr is the learning rate
public export
GA : Num pType => Neg pType => Random pType =>
  (mon : ComMonoid pType) => FromDouble pType =>
  {default 0.001 lr : pType} -> Optimiser (Const pType) Unit
GA = MkOptimiser
  (!% \(p, ()) => (p ** \p' => (p + lr * p', ())))
  (randomRIO (-1, 1))
  (pure ())

namespace Momentum
  public export
  momentumUpdate : Num pType => Neg pType =>
    {lr : pType} ->
    (gamma : pType) ->
    (p : pType) ->
    (s : pType) ->
    (p' : pType) ->
    (pType, pType)
  momentumUpdate gamma p s p' = let s' = gamma * s + p'
                                in (p - lr * s', s')

  public export
  lookAhead : Num pType =>
    (gamma, p, s : pType) ->
    pType
  lookAhead gamma p s = p + gamma * s
  
  ||| Gradient Descent with momentum, optionally with Nesterov acceleration
  public export
  GDMomentum : Num pType => Neg pType => Random pType =>
   (mon : ComMonoid pType) =>
   FromDouble pType =>
   {default False nesterov : Bool} ->
   {default 0.001 lr : pType} ->
   {default 0.9 gamma : pType} ->
   Optimiser (Const pType) pType
  GDMomentum = MkOptimiser
    (!% \(p, s) => (if nesterov then lookAhead gamma p s else p
                   ** momentumUpdate {lr} gamma p s))
    (randomRIO (-1, 1))
    (pure 0)
  
namespace Adam
  ||| Adam update step
  ||| State is (m, v, beta1^t, beta2^t) where m and v are the first and second
  ||| moment estimates, and beta1^t, beta2^t are running powers for bias correction
  public export
  adamUpdate : Num pType => Neg pType => Fractional pType => Sqrt pType =>
    {lr : pType} ->
    (beta1 : pType) ->
    (beta2 : pType) ->
    (epsilon : pType) ->
    (p : pType) ->
    (m : pType) ->
    (v : pType) ->
    (b1p : pType) ->
    (b2p : pType) ->
    (g : pType) ->
    (pType, pType, pType, pType, pType)
  adamUpdate beta1 beta2 epsilon p m v b1p b2p g =
    let m' = beta1 * m + (1 - beta1) * g
        v' = beta2 * v + (1 - beta2) * g * g
        b1p' = b1p * beta1
        b2p' = b2p * beta2
        mHat = m' / (1 - b1p')
        vHat = v' / (1 - b2p')
    in (p - lr * mHat / (sqrt vHat + epsilon), m', v', b1p', b2p')

  ||| Adam optimiser (Kingma & Ba, 2014)
  ||| Using 4 parameters for state for efficiency
  ||| @lr is the learning rate
  ||| @beta1 is the exponential decay rate for the first moment estimate
  ||| @beta2 is the exponential decay rate for the second moment estimate
  ||| @epsilon is a small constant for numerical stability
  public export
  Adam : Num pType => Neg pType => Random pType =>
   (mon : ComMonoid pType) =>
   FromDouble pType =>
   Fractional pType => Sqrt pType =>
   {default 0.001 lr : pType} ->
   {default 0.9 beta1 : pType} ->
   {default 0.999 beta2 : pType} ->
   {default 1.0e-8 epsilon : pType} ->
   Optimiser (Const pType) (pType, pType, pType, pType)
  Adam = MkOptimiser
    (!% \(p, (m, v, b1p, b2p)) =>
      (p ** adamUpdate {lr} beta1 beta2 epsilon p m v b1p b2p))
    (randomRIO (-1, 1))
    (pure (0, 0, 1, 1))