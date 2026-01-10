module Control.Monad.Distribution

import Data.Vect
import Data.Vect.Quantifiers

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
  sample : Dist i -> m (Fin i)


-- public export
-- Logits : {tys : Vect i Type} -> Dist i -> Vect i Double
-- Logits (MkDist logits _) = logits
-- 
-- public export
-- Types : Dist i -> Vect i Type
-- Types (MkDist {tys} _ _) = tys
-- 
-- public export
-- Terms : (d : Dist i) -> HVect (Types d)
-- Terms (MkDist logits terms) = terms


-- ||| Convex combination of a finite set of types
-- public export
-- record Dist (tys : Vect n Type) where
--   constructor MkDist
--   logits : Vect n Double
