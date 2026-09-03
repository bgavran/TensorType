module Control.Monad.Distribution

import Data.Vect
import Data.Fin
import Data.Bag

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
||| Note that `0` is the canonical choice, as softargmax subtracts the max
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
Simplex name n = Const2 (Dist name n)
  (Tensor [name ~~> n] Double ** numIsMonoid)

||| Distributions are shown as probabilities (via softargmax), not as logits
public export
{axisName : AxisName} -> {i : Nat} -> Show (Dist axisName i) where
  show (MkDist xs) = show (softargmaxImpl xs)

||| A distribution over `n` branches together with, contingent on a choice made
||| by the environment, the chosen branch's content
||| TODO do we think of distr. on the fw pass as being part of Simplex or Nap?
public export
ProbabilisticChoice : {n : Nat} -> (distName : AxisName) -> 
  (branches : Vect n AddCont) -> AddCont
ProbabilisticChoice distName branches
  = Simplex distName n >*< (Vect n >-+@ Coproduct branches)

||| The choice made: a distribution over the branches and the chosen branch's content
public export
ChoiceMade : {n : Nat} -> (distName : AxisName) ->
  (branches : Vect n AddCont) -> AddCont
ChoiceMade distName branches = Simplex distName n >*< Coproduct branches

||| Resolve probabilistic choice through the ground truth label. The labelled 
||| branch is selected, and its gradient goes back as a singleton bag
||| TODO do we need the right component of the codomain?
public export
resolveByLabel : {distName : AxisName} ->
  {branches : Vect n AddCont} ->
  ProbabilisticChoice distName branches >*< ChoiceMade distName branches
    =%+> ChoiceMade distName branches >*< ChoiceMade distName branches
resolveByLabel = !%+ \((dist, ex), y@(distTrue, (iTrue ** _))) =>
  (((dist, index ex iTrue), y) ** \((d', g'), yGrad) =>
      ((d', MkBag [(iTrue ** g')]), yGrad))
