module Control.Monad.Distribution

import Data.Vect
import Data.Vect.Quantifiers
import Control.Monad.Identity
import Misc

||| Convex combination of a finite set of types
||| Since this is used in `Data.Container.Products.ConvexComb`, we cannot use
||| `Tensor` here
public export
data Dist : (i : Nat) -> Type where
  ||| To produce it, we need terms of those types, as well as
  ||| probabilities of each (represented as logits)
  MkDist : Vect i Double -> Dist i

||| Do we need `tys`?
public export
interface Monad m => MonadSample m where
  sample : {i : Nat} -> IsSucc i => Dist i -> m (Fin i)


||| Trivial sampler, always picks the first element
public export
[pickFirst] MonadSample (Identity) where
  sample {i = (S k)} (MkDist xs) = Id FZ

||| Max sampler, always picks the element with the highest logit
public export
[pickMax] MonadSample (Identity) where
  sample {i = (S k)} (MkDist xs) = Id (argmax xs)

||| Min sampler, always picks the element with the lowest logit
public export
[pickMin] MonadSample (Identity) where
  sample {i = (S k)} (MkDist xs) = Id (argmin xs)

-- ||| Convex combination of a finite set of types
-- public export
-- record Dist (tys : Vect n Type) where
--   constructor MkDist
--   logits : Vect n Double
