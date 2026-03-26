module Control.Monad.Distribution

import Data.Vect
import Data.Vect.Quantifiers
import Control.Monad.Identity
import System.Random

import Data.Num
import Misc

||| Convex combination of a finite set of types, a point in a simplex △^(i-1)
||| i=2 -> △¹ -> line segment
||| i=3 -> △² -> triangle
||| ...
||| Probabilities are here represented as logits
||| Since this is used in `Data.Container.Products.ConvexComb`, we cannot use
||| `Tensor` here
public export
data Dist : (i : Nat) -> Type where
  ||| Probabilities are represented as logits
  MkDist : Vect i Double -> Dist i

public export
toVect : Dist i -> Vect i Double
toVect (MkDist xs) = xs

||| Logit representation of the uniform distribution
public export
uniform : {i : Nat} -> (isSucc : IsSucc i) => Dist i
uniform = MkDist (replicate i 0)

||| Logit representation of dirac delta
public export
diracDelta : {i : Nat} -> IsSucc i =>
  (j : Fin i) -> Dist i
diracDelta @{ItIsSucc {n}} j = MkDist $ insertAt j 0 (replicate n minusInfinity)
