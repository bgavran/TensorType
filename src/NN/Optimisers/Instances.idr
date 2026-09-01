module NN.Optimisers.Instances

import Data.Materialise
import Data.Container.Additive
import Data.Num
import NN.Optimisers.Definition
import NN.Utils

||| Gradient descent optimiser. Has trivial state
||| @lr is the learning rate
public export
GD : Neg pType =>
  (mon : ComMonoid pType) => FromDouble pType =>
  {default 0.001 lr : pType} -> Optimiser (Const pType) Unit
GD = MkOptimiser
  (!% \(p, ()) => (p ** \p' => (p - lr * p', ())))
  (pure ())

||| Gradient ascent optimiser. Has trivial state
||| @lr is the learning rate
public export
GA : Neg pType =>
  (mon : ComMonoid pType) => FromDouble pType =>
  {default 0.001 lr : pType} -> Optimiser (Const pType) Unit
GA = MkOptimiser
  (!% \(p, ()) => (p ** \p' => (p + lr * p', ())))
  (pure ())

namespace Momentum
  public export
  momentumUpdate : Neg pType =>
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
  GDMomentum : Neg pType =>
   (mon : ComMonoid pType) =>
   FromDouble pType =>
   {default False nesterov : Bool} ->
   {default 0.001 lr : pType} ->
   {default 0.9 gamma : pType} ->
   Optimiser (Const pType) pType
  GDMomentum = MkOptimiser
    (!% \(p, s) => (if nesterov then lookAhead gamma p s else p
                   ** momentumUpdate {lr} gamma p s))
    (pure 0)
  
namespace Adam
  ||| Adam step. The moments are parameter-shaped; the bias-correction powers
  ||| beta^t are the same scalar at every coordinate, so they are `Double`
  public export
  adamUpdate : Neg pType => Fractional pType => Sqrt pType =>
    FromDouble pType => Materialise pType =>
    {lr : pType} ->
    (beta1 : Double) ->
    (beta2 : Double) ->
    (epsilon : pType) ->
    (p : pType) ->
    (m : pType) ->
    (v : pType) ->
    (b1p : Double) ->
    (b2p : Double) ->
    (g : pType) ->
    (pType, pType, pType, Double, Double)
  adamUpdate beta1 beta2 epsilon p m v b1p b2p g =
    let g' = materialise g
        m' = materialise (fromDouble beta1 * m + fromDouble (1 - beta1) * g')
        v' = materialise (fromDouble beta2 * v + fromDouble (1 - beta2) * g' * g')
        b1p' = b1p * beta1
        b2p' = b2p * beta2
        mHat = fromDouble (1 / (1 - b1p')) * m'
        vHat = fromDouble (1 / (1 - b2p')) * v'
    in (p - lr * mHat / (sqrt vHat + epsilon), m', v', b1p', b2p')

  ||| Adam optimiser (Kingma & Ba, 2014)
  ||| State: the two moments and the two scalar bias-correction powers
  ||| @lr is the learning rate
  ||| @beta1 is the exponential decay rate for the first moment estimate
  ||| @beta2 is the exponential decay rate for the second moment estimate
  ||| @epsilon is a small constant for numerical stability
  public export
  Adam : Neg pType =>
   (mon : ComMonoid pType) =>
   FromDouble pType => Materialise pType =>
   Fractional pType => Sqrt pType =>
   {default 0.001 lr : pType} ->
   {default 0.9 beta1 : Double} ->
   {default 0.999 beta2 : Double} ->
   {default 1.0e-8 epsilon : pType} ->
   Optimiser (Const pType) (pType, pType, Double, Double)
  Adam = MkOptimiser
    (!% \(p, (m, v, b1p, b2p)) =>
      (p ** adamUpdate {lr} beta1 beta2 epsilon p m v b1p b2p))
    (pure (0, 0, 1, 1))