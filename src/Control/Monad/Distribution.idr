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
||| TODO change description, as now `Dist` involves containers
||| TODO, is Dist a quotient container?
public export
record Dist (a : Axis) where
  constructor MkDist
  ||| Probabilities are represented as logits
  logits : Tensor [a] Double

||| Logit representation of the uniform distribution
||| Is defined for a container once the choice of shape is made
public export
uniform : {a : Axis} -> (s : a.cont.Shp) -> Dist a
uniform s = MkDist (fillAt (shapeToRank1Shape s) 0)

||| Logit representation of dirac delta at the position `p` of the shape `s`
||| Note that `0` is the canonical choice, as softargmax subtracts the max
public export
diracDelta : {a : Axis} -> IsDecidable a.cont =>
  (s : a.cont.Shp) -> a.cont.Pos s -> Dist a
diracDelta s p = MkDist $ fillAt (shapeToRank1Shape s) minusInfinity // [p] .~ 0

||| Naperian axes have a single shape (`()`), so we do not need to supply it
namespace Naperian
  public export
  uniform : {a : Axis} -> IsNaperian a => Dist a
  uniform @{MkIsNaperian _ _} = uniform ()

  public export
  diracDelta : {a : Axis} -> IsNaperian a => DecEq (Log a) => Log a -> Dist a
  diracDelta @{MkIsNaperian _ _} p = diracDelta () p

namespace Cont
  ||| Container whose choice of a shape is a distribution over some choices, 
  ||| and a position is a specific choice made.
  public export
  Dist : Axis -> Cont
  Dist a = (d : Dist a) !> a.cont.Pos d.logits.extractShapeRank1

public export
uniformLens : {a : Axis} -> a.cont =%> Cont.Dist a
uniformLens = !% \s => (uniform s ** id)

||| Container whose shapes are distributions (over positions over some chosen
||| container shape), and positions are their gradients.
||| Both are represented as logits
||| If we were treating this as non-logit distributions then we'd have a
||| one less dimension: both for the simplex in the forward pass and the
||| gradients in the backwards one
||| That is, the effective dimension of this space is n-1 (we can add a
||| constant to all logits without changing the answer), and there's a
||| direction in the gradient logit space that does not affect output
public export
Simplex : Axis -> AddCont
Simplex a = MkAddCont
  (Dist a) (\d =>
    (Tensor [a.name ~> At d.logits.extractShapeRank1] Double ** numIsMonoid))

||| Distributions are shown as probabilities (via softargmax), not as logits
public export
{a : Axis} ->
AllDisplay2D [a] Double =>
IsFoldable a.cont =>
AllAlgebra [a] Double =>
TensorCubEvidence [a] =>
Show (Dist a) where
  show (MkDist xs) = show (softargmaxImpl xs)

||| A distribution over a container of branches, together with answers ready 
||| when any branch is chosen, computed only when the branch is asked for
||| TODO do we think of distr. on the fw pass as being part of Simplex or Nap?
public export
ProbabilisticChoice : (a : Axis) -> a.cont.filledWith AddCont -> AddCont
ProbabilisticChoice a branches
  = Simplex (a.name ~> At (shapeExt branches)) >*< Section (index branches)

||| Each probabilistic choice can be turned into a sequence of producing a 
||| distribution, waiting for the response from the environment about which 
||| choice to make, then making that choice
public export
pendingChoice : {a : Axis} ->
  (branches : a.cont.filledWith AddCont) ->
  ProbabilisticChoice a branches =%+> Dist a >-+@ AddContDPair (index branches)
pendingChoice branches =
  let Choice : AddCont
      Choice = Simplex (a.name ~> At (shapeExt branches))
  in (id {c = Choice} >*< graph) %+>> distribute
  {c = Simplex (a.name ~> At (shapeExt branches)),
   g = AddContDPair (index branches)} (\d => !% \_ =>
  (MkDist (MkT ((shapeExt branches <| const ()) <| \pp =>
     index (GetT d.logits) (fst pp ** ()))) ** id))