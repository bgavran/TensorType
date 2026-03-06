module Data.Container.Base.Product.Definitions

import Data.DPair
import Decidable.Equality
import Data.Vect
import Data.List.Quantifiers
import Data.Vect.Quantifiers

import Data.Container.Base.Object.Definition
import Data.Container.Base.Morphism.Definition
import Data.Container.Base.Extension.Definition
import Data.Container.Base.Quantifiers

import Control.Monad.Distribution

import Misc

public export infixr 3 ><  -- Hancock tensor product
public export infixr 3 >*< -- categorical product
public export infixr 3 >+< -- coproduct
public export infixr 3 >@  -- composition
public export infixr 3 @>
public export infixr 3 <%> 

||| Categorical product of containers
||| Monoid with UnitCont
namespace Product
  ||| Binary version of product
  public export
  (>*<) : Cont -> Cont -> Cont
  c1 >*< c2 = ((s, s') : (c1.Shp, c2.Shp)) !> Either (c1.Pos s) (c2.Pos s')

  namespace List
    ||| N-ary version of product
    public export
    AllAny : List Cont -> Cont
    AllAny xs = (shapes : All Shp xs) !> AnyPos shapes

  namespace Vect
    ||| N-ary version of product
    public export
    AllAny : Vect n Cont -> Cont
    AllAny xs = (shapes : All Shp xs) !> AnyPos shapes


||| Non-categorical product of containers, often also called
||| 'Hancock' (Scotland), 'Dirichlet' (Spivak), or 'Tensor product' (various)
||| Monoid with CUnit
namespace HancockTensorProduct
  public export
  (><) : Cont -> Cont -> Cont
  c1 >< c2 = (ss : (c1.Shp, c2.Shp)) !> (c1.Pos (fst ss), c2.Pos (snd ss))

  namespace List
    ||| N-ary version of tensor product
    public export
    AllAny : List Cont -> Cont
    AllAny xs = (shapes : All Shp xs) !> AllPos shapes

  namespace Vect
    ||| N-ary version of tensor product
    public export
    AllAll : Vect n Cont -> Cont
    AllAll xs = (shapes : All Shp xs) !> AllPos shapes

  namespace Morphism
    ||| Action on morphisms
    public export
    (><) : (c1 =%> d1) -> (c2 =%> d2) -> (c1 >< c2) =%> (d1 >< d2)
    (><) f g = !% \(c, d) => ((f.fwd c, g.fwd d) **
      \(c', d') => (f.bwd c c', g.bwd d d'))

    namespace Monadic
      public export
      (><) : {m : Type -> Type} -> Monad m =>
        {c1, d1, c2, d2 : Cont} ->
        MLens {m=m} c1 d1 -> MLens {m=m} c2 d2 -> MLens {m=m} (c1 >< c2) (d1 >< d2)
      (><) f g = !%% \(c, d) => do
        (x ** kx) <- (%%! f) c
        (y ** ky) <- (%%! g) d
        pure ((x, y) ** \x'y' => (kx (fst x'y'), ky (snd x'y')))

  ||| Dependent Hancock (tensor) product of containers.
  ||| This is the analogue of DPair for containers:
  ||| Given a container `pc` and a family `qc : pc.Shp -> Cont`,
  ||| form the container whose shapes are dependent pairs of shapes
  ||| and positions are pairs of positions.
  public export
  DepHancockProduct : (pc : Cont) -> (qc : pc.Shp -> Cont) -> Cont
  DepHancockProduct pc qc = 
    ((p ** q) : DPair pc.Shp (Shp . qc)) !> (pc.Pos p, (qc p).Pos q)


||| Coproduct of containers
||| Monoid with Empty
namespace Coproduct
  public export
  (>+<) : Cont -> Cont -> Cont
  c1 >+< c2 = (es : Either c1.Shp c2.Shp) !> either c1.Pos c2.Pos es

  namespace List
    ||| N-ary version of coproduct
    public export
    Any : List Cont -> Cont
    Any xs = (shapes : Any Shp xs) !> AnyShpPos shapes

  namespace Vect
    ||| N-ary version of coproduct
    public export
    Any : Vect n Cont -> Cont
    Any xs = (shapes : Any Shp xs) !> AnyShpPos shapes

namespace Composition
  ||| Composition of containers making Ext (c >@ d) = (Ext c) . (Ext d)
  ||| Non-symmetric in general, and not in diagrammatic order
  ||| Monoid with Scalar
  public export
  (>@) : Cont -> Cont -> Cont
  c >@ d = (ex : Ext c d.Shp) !>
    (cp : c.Pos (shapeExt ex) ** d.Pos (index ex cp))
  
  ||| Diagrammatic composition of containers
  public export
  (@>) : Cont -> Cont -> Cont
  c @> d = (ex : Ext d c.Shp) !>
    (dp : d.Pos (shapeExt ex) ** c.Pos (index ex dp))

  namespace Morphism
    ||| Action on morphisms
    public export
    (>@) : (c1 =%> d1) -> (c2 =%> d2) -> (c1 >@ c2) =%> (d1 >@ d2)
    (>@) f g = !% \(s <| idx) => (f.fwd s <| g.fwd . idx . f.bwd s **
      \(dp ** dp2) => (f.bwd s dp ** g.bwd (idx (f.bwd s dp)) dp2))

    ||| Action on morphisms for diagrammatic composition
    public export
    (@>) : (c1 =%> c2) -> (d1 =%> d2) -> (c1 @> d1) =%> (c2 @> d2)
    (@>) f g = !% \(s <| idx) => (g.fwd s <| f.fwd . idx . g.bwd s **
      \(dp ** dp2) => (g.bwd s dp ** f.bwd (idx (g.bwd s dp)) dp2))

||| Closure with respect to the Hancock tensor product
namespace MonoidalClosure
  ||| Every lens gives rise to a container
  ||| The set of shapes is the lens itself
  ||| The set of positions is the inputs to the lens
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

||| Closure with respect to the Cartesian product
namespace CartesianClosure
  ||| From https://www.cs.ox.ac.uk/people/samuel.staton/papers/cie10.pdf
  public export
  CartesianClosure : Cont -> Cont -> Cont
  CartesianClosure c d
    = (f : ((x : c.Shp) -> (y : d.Shp ** d.Pos y -> Maybe (c.Pos x))))
      !> (xx : c.Shp ** yy' : d.Pos (fst (f xx)) ** ?cartesianClosureImpl)


-- Not exactly a product
public export
List : Cont -> Cont
List c = (ss : List (c.Shp)) !> All c.Pos ss



||| If `f` is a monad, then `f <!> -` is a comonad, and vice versa
public export
(<!>) : (f : Type -> Type) -> Cont -> Cont
(<!>) f c = (s : c.Shp) !> (f (c.Pos s))

public export infixr 9 <!>

namespace Morphism
  public export
  (<!>) : (f : Type -> Type) -> Functor f =>
    (c =%> d) ->
    ((f <!> c) =%> (f <!> d))
  (<!>) f l = !% \x => (l.fwd x ** ((l.bwd x) <$>) )

  public export infixr 9 <!>

||| BANG. List on positions, always has a monoid structure
public export
(!!) : Cont -> Cont
(!!) = (List <!>)

export prefix 9 !!


||| TODO Might be able to delete this and leave just the definition in Additive?
public export
PreparedChoice : {n : Nat} -> Vect n Cont -> Cont
PreparedChoice xs = !! (AllAny xs)


namespace ConvexCombProduct
  public export
  Simplex : Nat -> Cont
  Simplex n = (_ : Dist n) !> (Vect n Double)

  ||| Probabilistic product of containers
  ||| Convex combination of shapes, and a product of positions
  ||| This is equivalent to the n-ary Hancock tensor product of containers, 
  ||| together with a choice of a point inside an n-simplex
  public export
  ConvexComb : {n : Nat} -> (xs : Vect n Cont) -> Cont
  ConvexComb xs = Simplex n >< PreparedChoice xs


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