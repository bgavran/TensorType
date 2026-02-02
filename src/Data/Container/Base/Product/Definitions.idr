module Data.Container.Base.Product.Definitions

import Data.DPair
import Decidable.Equality
import Data.Vect
import Data.Vect.Quantifiers

import Data.Container.Base.Object.Definition
import Data.Container.Base.Morphism.Definition
import Data.Container.Base.Extension.Definition
import Control.Monad.Distribution

import Misc

public export infixr 0 ><
public export infixr 0 >*<
public export infixr 0 >+<
public export infixr 0 >@
public export infixr 0 <%>

||| Categorical product of containers
||| Monoid with UnitCont
public export
(>*<) : Cont -> Cont -> Cont
c1 >*< c2 = ((s, s') : (c1.Shp, c2.Shp)) !> Either (c1.Pos s) (c2.Pos s')

||| Non-categorical product of containers, often also called
||| 'Hancock' (Scotland), 'Dirichlet' (Spivak), or 'Tensor product' (various)
||| Monoid with CUnit
namespace HancockTensorProduct
  public export
  (><) : Cont -> Cont -> Cont
  c1 >< c2 = (ss : (c1.Shp, c2.Shp)) !> (c1.Pos (fst ss), c2.Pos (snd ss))

  public export
  hancockMap : (c1 =%> d1) -> (c2 =%> d2) -> (c1 >< c2) =%> (d1 >< d2)
  hancockMap f g = !% \(c, d) => ((f.fwd c, g.fwd d) **
    \(c', d') => (f.bwd c c', g.bwd d d'))


||| Coproduct of containers
||| Monoid with Empty
public export
(>+<) : Cont -> Cont -> Cont
c1 >+< c2 = (es : Either c1.Shp c2.Shp) !> either c1.Pos c2.Pos es

||| Composition of containers making Ext (c >@ d) = (Ext c) . (Ext d)
||| Non-symmetric in general, and not in diagrammatic order
||| Monoid with Scalar
public export
(>@) : Cont -> Cont -> Cont
c >@ d = (ex : Ext c d.Shp) !> (cp : c.Pos (shapeExt ex) ** d.Pos (index ex cp))

public export infixr 0 @>

||| Diagrammatic composition of containers
public export
(@>) : Cont -> Cont -> Cont
c @> d = (ex : Ext d c.Shp) !> (dp : d.Pos (shapeExt ex) ** c.Pos (index ex dp))

namespace MonoidalClosure
  ||| Every lens gives rise to a container
  ||| The set of shapes is the lens itself
  ||| The set of positions is the inputs to the lens
  ||| This is the closure with respect to the Hancock tensor product
  public export
  InternalLens : Cont -> Cont -> Cont
  InternalLens c d
    = (f : c =%> d)
      !> (xx : c.Shp ** d.Pos ((f.fwd xx)))

  public export
  curry : (c >< d) =%> e -> c =%> (InternalLens d e)
  curry f = !% \x => (!% \y => (f.fwd (x, y) ** snd . f.bwd (x, y)) **
    \(y ** e') => fst (f.bwd (x, y) e'))

  public export
  uncurry : c =%> (InternalLens d e) -> (c >< d) =%> e
  uncurry f = !% \(x, y) => ((f.fwd x).fwd y **
    \e' => (f.bwd x (y ** e'), (f.fwd x).bwd y e'))

namespace CartesianClosure
  ||| From https://www.cs.ox.ac.uk/people/samuel.staton/papers/cie10.pdf
  public export
  CartesianClosure : Cont -> Cont -> Cont
  CartesianClosure c d
    = (f : ((x : c.Shp) -> (y : d.Shp ** d.Pos y -> Maybe (c.Pos x))))
      !> (xx : c.Shp ** yy' : d.Pos (fst (f xx)) ** ?cartesianClosureImpl)


||| Dependent Hancock (tensor) product of containers.
||| This is the analogue of DPair for containers:
||| Given a container `pc` and a family `qc : pc.Shp -> Cont`,
||| form the container whose shapes are dependent pairs of shapes
||| and positions are pairs of positions.
public export
DepHancockProduct : (pc : Cont) -> (qc : pc.Shp -> Cont) -> Cont
DepHancockProduct pc qc = 
  ((p ** q) : DPair pc.Shp (Shp . qc)) !> (pc.Pos p, (qc p).Pos q)

public export
data AllPos : {cs : Vect n Cont} -> All Shp cs -> Type where
  Nil : AllPos []
  (::) : {0 cs : Vect m Cont} -> {0 ss : All Shp cs} ->
    Pos c s -> AllPos {cs=cs} ss -> AllPos {cs=(c::cs)} (s :: ss)


||| Probabilistic product of containers
||| Convex combination of shapes, and a product of positions
||| This is equivalent to the n-ary Hancock tensor product of containers, 
||| together with a choice of a point inside an n-simplex
public export
ConvexComb : {n : Nat} -> Vect n Cont -> Cont
ConvexComb xs = ((p, shp) : (Dist n, All Shp xs)) !> AllPos shp

-- DCont : (n : Nat) -> Cont
-- DCont n = (_ : Dist n) !> Unit
-- 
-- ProdCont : Vect n Cont -> Cont 
-- ProdCont xs = (ys : All Shp xs) !> AllPos ys
-- 
-- DistCont : Vect n Cont -> Cont
-- DistCont xs = ProdCont xs >< DCont

--(<%>) : Cont -> Cont -> Cont
--c <%> d = (Tensor [2] Double, (c1.Shp, c2.Shp)) !> 


||| Derivative of a container
||| Given c=(Shp !> pos) the derivative can be thought of as
||| a shape s : Shp, a distinguished position p : pos s, and the set of *all other positions*
public export
Deriv : (c : Cont) ->
  InterfaceOnPositions c DecEq =>
  Cont
Deriv (shp !> pos) @{MkI}
  = ((s ** p) : DPair shp pos) !> (p' : pos s ** IsNo (decEq p p'))

public export
pairExtensions : Ext c a -> Ext d b -> Ext (c >< d) (a, b)
pairExtensions (shapeC <| indexC) (shapeD <| indexD)
  = (shapeC, shapeD) <| \(posC, posD) => (indexC posC, indexD posD)