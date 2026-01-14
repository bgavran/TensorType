module Control.Monad.Distribution

import Data.Vect
import Data.Vect.Quantifiers
import Control.Monad.Identity
import Misc
import System.Random

||| Convex combination of a finite set of types
||| Since this is used in `Data.Container.Products.ConvexComb`, we cannot use
||| `Tensor` here
public export
data Dist : (i : Nat) -> Type where
  ||| Probabilities are represented as logits
  MkDist : Vect i Double -> Dist i