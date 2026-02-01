module NN.Optimisers.Instances

import Data.Container.Additive
import NN.Optimisers.Definition

||| Gradient descent optimiser. Has trivial state
||| @lr is the learning rate
public export
GD : Num pType => Neg pType =>
  {lr : pType} -> Optimiser (Const pType) Unit
GD = MkOptimiser $ !% \(p, ()) => (p ** \p' => (p - lr * p', ()))

||| Gradient ascent optimiser. Has trivial state
||| @lr is the learning rate
public export
GA : Num pType =>
  {lr : pType} -> Optimiser (Const pType) Unit
GA = MkOptimiser $ !% \(p, ()) => (p ** \p' => (p + lr * p', ()))

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
  
  
  ||| Gradient Descent with momentum
  public export
  GDMomentum : Num pType => Neg pType =>
   {lr : pType} ->
   {gamma : pType} ->
   Optimiser (Const pType) pType
  GDMomentum = MkOptimiser $
    !% \(p, s) => (p ** momentumUpdate {lr} gamma p s)
  

  public export
  lookAhead : Num pType =>
    (gamma, p, s : pType) ->
    pType
  lookAhead gamma p s = p + gamma * s
 
  ||| Gradient descent with Nesterov momentum
  public export
  GDNesterovMomentum : Num pType => Neg pType =>
   {lr : pType} ->
   {gamma : pType} ->
   Optimiser (Const pType) pType
  GDNesterovMomentum = MkOptimiser $
    !% \(p, s) => (lookAhead gamma p s ** momentumUpdate {lr} gamma p s)