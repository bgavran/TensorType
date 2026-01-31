module NN.Optimisers.Instances

import Data.Container
import Data.Autodiff.AdditiveContainer
import NN.Optimisers.Definition

||| Gradient descent optimiser. Has trivial state
||| @lr is the learning rate
public export
GD : Num pType => Neg pType =>
  (lr : pType) -> Optimiser (\_ => Const pType) Unit
GD lr = MkOptimiser $ \_ =>
  !% \(p, ()) => (p ** \p' => (p - lr * p', ()))

||| Gradient ascent optimiser. Has trivial state
||| @lr is the learning rate
public export
GA : Num pType =>
  (lr : pType) -> Optimiser (\_ => Const pType) Unit
GA lr = MkOptimiser $ \_ =>
  !% \(p, ()) => (p ** \p' => (p + lr * p', ()))

namespace Momentum
  public export
  momentumUpdate : Num pType => Neg pType =>
    (gamma : pType) ->
    (p : pType) ->
    (s : pType) ->
    (p' : pType) ->
    (pType, pType)
  momentumUpdate gamma p s p' = let s' = - gamma * s + p'
                                in (p + s', s')
  
  
  ||| Gradient Descent with momentum
  public export
  GDMomentum : Num pType => Neg pType =>
   (lr : pType) ->
   (gamma : pType) ->
   Optimiser (\_ => Const pType) pType
  GDMomentum lr gamma = MkOptimiser $ \_ =>
    !% \(p, s) => (p ** momentumUpdate gamma p s)
  

  public export
  lookAhead : Num pType =>
    (gamma, p, s : pType) ->
    pType
  lookAhead gamma p s = p + gamma * s
 
  ||| Gradient descent with Nesterov momentum
  public export
  GDNesterovMomentum : Num pType => Neg pType =>
   (lr : pType) ->
   (gamma : pType) ->
   Optimiser (\_ => Const pType) pType
  GDNesterovMomentum lr gamma = MkOptimiser $ \_ =>
    !% \(p, s) => (lookAhead gamma p s ** momentumUpdate gamma p s)