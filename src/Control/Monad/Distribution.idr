module Control.Monad.Distribution

import Data.Vect

import Data.Num
import public Data.Tensor
import Data.Container.Additive

||| Convex combination of a finite set of types, a point in a simplex △^(i-1)
||| i=2 -> △¹ -> line segment
||| i=3 -> △² -> triangle
||| ...
||| Probabilities are represented as logits, represented as a rank 1 tensor.
||| Because the tensor has a name, and `Dist` is a thin wrapper around it,
||| the name is exposed at the type level, allowing named operations to be
||| extended to distributions
||| TODO, is Dist a quotient container?
public export
record Dist (name : AxisName) (i : Nat) where
  constructor MkDist
  ||| Probabilities are represented as logits
  logits : Tensor [name ~~> i] Double

||| Logit representation of the uniform distribution
public export
uniform : {name : AxisName} -> {i : Nat} ->
  (isSucc : IsSucc i) => Dist name i
uniform = MkDist (fill 0)

||| Logit representation of dirac delta
public export
diracDelta : {name : AxisName} -> {i : Nat} ->
  IsSucc i =>
  (j : Fin i) -> Dist name i
diracDelta @{ItIsSucc {n}} j
  = MkDist (># (insertAt j 0 (replicate n minusInfinity)))

namespace Cont
  ||| Container whose shape represents a distribution over `n` choices, and
  ||| whose position represents the choice made.
  public export
  Dist : AxisName -> Nat -> Cont
  Dist name n = Const2 (Dist name n) (Fin n)

||| Container whose shapes are distributions, positions their gradients.
||| Both are represented as logits
||| If we were treating this as non-logit distributions then we'd have a
||| one less dimension: both for the simplex in the forward pass and the
||| gradients in the backwards one
||| That is, the effective dimension of this space is n-1 (we can add a
||| constant to all logits without changing the answer), and there's a
||| direction in the gradient logit space that does not affect output
public export
Simplex : AxisName -> Nat -> AddCont
Simplex name n = MkAddCont $ (_ : Dist name n) !> (Tensor [name ~~> n] Double)

||| Distributions are shown as probabilities (via softargmax), not as logits
public export
{axisName : AxisName} -> {i : Nat} -> Show (Dist axisName i) where
  show (MkDist xs) = show (softargmaxImpl xs)
