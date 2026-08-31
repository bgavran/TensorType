module Data.Container.Base.Product.Definition

import Data.DPair
import Decidable.Equality
import Data.Either
import Data.Vect
import Data.List.Quantifiers
import Data.Vect.Quantifiers

import Data.Container.Base.Object.Definition
import Data.Container.Base.Morphism.Definition
import Data.Container.Base.Extension.Definition
import Data.Container.Base.Properties.Definition
import Data.Container.Base.Endofunctor.Definition


import Data.Container.Base.Quantifiers

import Data.ComMonoid

import Misc

public export infixr 3 ><  -- Hancock tensor product
public export infixr 3 >*< -- categorical product
public export infixr 3 >+< -- coproduct
public export infixr 3 >@  -- composition
public export infixr 3 @>
public export infixr 3 <%> 

||| Categorical product of containers
||| Monoid with UnitCont
||| It holds that `Ext (c1 >*< c2) a = (Ext c1) × (Ext c2)` where
||| `×` is the pointwise product of functors.
namespace CategoricalProduct
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

  ||| "Dependent categorical product": 
  ||| Dependent pair type for the categorical product of containers
  ||| Given a container `s` and a family `p : s.Shp -> Cont`,
  ||| form the container whose shapes are dependent pairs of shapes
  ||| and a position is either a position of s or a position of p.
  public export
  DPairCart : (s : Cont) -> (p : s.Shp -> Cont) -> Cont
  DPairCart s p = ((sShp ** pShp) : DPair s.Shp (Shp . p))
    !> Either (s.Pos sShp) ((p sShp).Pos pShp)


||| Non-categorical product of containers, often also called
||| 'Hancock' (Scotland), 'Dirichlet' (Spivak), or 'Tensor product' (various)
||| Monoid with Scalar
||| It holds that `Ext (c1 >< c2) a = (Ext c1) ⊗ (Ext c2)` where
||| `⊗` is the day convolution product of functors.
namespace HancockTensorProduct
  public export
  (><) : Cont -> Cont -> Cont
  c1 >< c2 = (ss : (c1.Shp, c2.Shp)) !> (c1.Pos (fst ss), c2.Pos (snd ss))

  namespace List
    ||| N-ary version of tensor product
    public export
    AllAll : List Cont -> Cont
    AllAll xs = (shapes : All Shp xs) !> AllPos shapes

  namespace Vect
    ||| N-ary version of tensor product
    public export
    AllAll : Vect n Cont -> Cont
    AllAll xs = (shapes : All Shp xs) !> AllPos shapes

  namespace Morphism
    ||| Action on morphisms
    public export
    (><) : (c1 =%> d1) -> (c2 =%> d2) -> (c1 >< c2) =%> (d1 >< d2)
    (><) f g = !% \(c, d) =>
      let (c1 ** fk) = (%!) f c
          (d1 ** gk) = (%!) g d
      in ((c1, d1) ** \(c', d') => (fk c', gk d'))

  ||| "Dependent tensor product": 
  ||| Dependent pair type for the tensor product of containers
  ||| Given a container `s` and a family `p : s.Shp -> Cont`,
  ||| form the container whose shapes are dependent pairs of shapes
  ||| and positions are pairs of positions.
  public export
  DPairTensor : (s : Cont) -> (p : s.Shp -> Cont) -> Cont
  DPairTensor s p = 
    ((sShp ** pShp) : DPair s.Shp (Shp . p)) !> (s.Pos sShp, (p sShp).Pos pShp)

||| Coproduct of containers
||| Monoid with Empty
||| It holds that `Ext (c1 >+< c2) a = (Ext c1) + (Ext c2)` where
||| `+` is the pointwise cproduct of functors.
namespace CategoricalCoproduct
  ||| Binary version of coproduct
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

  namespace Morphism
    public export
    (>+<) : c1 =%> d1 -> c2 =%> d2 -> c1 >+< c2 =%> d1 >+< d2
    (>+<) f g = !% \case
      Left x => (Left (f.fwd x) ** f.bwd x)
      Right y => (Right (g.fwd y) ** g.bwd y)

namespace CompositionProduct
  ||| Container used to produce the position type in the compositon product
  public export
  positionCont : {c, d : Cont} -> Ext c d.Shp -> Cont
  positionCont ex = (cp : c.Pos (shapeExt ex)) !> d.Pos (index ex cp)
  
  ||| Composition of containers making Ext (c >@ d) = (Ext c) . (Ext d)
  ||| Non-symmetric in general, and not in diagrammatic order
  ||| Monoid with Scalar
  public export
  (>@) : Cont -> Cont -> Cont
  c >@ d = (ex : Ext c d.Shp) !> DPair (positionCont ex)

  ||| Diagrammatic composition of containers, i.e. swapped order of composition
  public export
  (@>) : Cont -> Cont -> Cont
  c @> d = (ex : Ext d c.Shp) !>
           DPair ((dp : d.Pos (shapeExt ex)) !> c.Pos (index ex dp))
           -- (DPair (d.Pos (shapeExt ex)) (c.Pos . index ex))
           -- (dp : d.Pos (shapeExt ex) ** c.Pos (index ex dp))

  namespace Morphism
    ||| Action on morphisms
    public export
    (>@) : c1 =%> d1 -> c2 =%> d2 -> c1 >@ c2 =%> d1 >@ d2
    (>@) f g = !% \ex =>
      (f.fwd (shapeExt ex) <| g.fwd . (index ex) . f.bwd (shapeExt ex) **
      \(dp ** dp2) => (f.bwd (shapeExt ex) dp ** g.bwd ((index ex) (f.bwd (shapeExt ex) dp)) dp2))

    ||| Action on morphisms for diagrammatic composition
    public export
    (@>) : c1 =%> c2 -> d1 =%> d2 -> c1 @> d1 =%> c2 @> d2
    (@>) f g = !% \(s <| idx) => (g.fwd s <| f.fwd . idx . g.bwd s **
      \(dp ** dp2) => (g.bwd s dp ** f.bwd (idx (g.bwd s dp)) dp2))

  -- ||| Action on morphisms
  -- public export
  -- compositionMap : (c1 =%> d1) -> (c2 =%> d2) -> (c1 >@ c2) =%> (d1 >@ d2)
  -- compositionMap f g = !% \(c1Shp <| c2Index) =>
  --   ((fst ((%!) f c1Shp) <| \d1Pos =>
  --     let gOut  = (%!) g (c2Index (snd ((%!) f c1Shp) d1Pos))
  --     in fst gOut) ** \(d1Pos ** d2Pos) => (snd ((%!) f c1Shp) d1Pos **
  --       snd ((%!) g (c2Index (snd ((%!) f c1Shp) d1Pos))) d2Pos))

||| Closure with respect to the Hancock tensor product
namespace MonoidalClosure
  ||| Every lens gives rise to a container
  ||| The set of shapes is the lens itself
  ||| The set of positions is the inputs to the lens
  public export
  InternalLens : Cont -> Cont -> Cont
  InternalLens c d = (f : c =%> d) !> DPair (lensInputs f)

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
    = (f : (Maybe <!> c) =%> d)
        !> (x : c.Shp ** y' : d.Pos (f.fwd x) ** IsNothing (f.bwd x y'))
      -- !> (xy' : DPair (lensInputs f) ** IsNothing (f.bwd (fst xy') (snd xy'))) 
  

  public export
  curry : c >*< d =%> e -> c =%> (CartesianClosure d e)
  curry f = !% \x => (!% \y => (f.fwd (x, y) ** \z' => eitherToMaybe
    (f.bwd (x, y) z')) ** bwPart) where
      bwPart : {x : c.Shp} ->
        (y : d.Shp ** z' : e.Pos (f.fwd (x, y)) ** IsNothing (eitherToMaybe (f.bwd (x, y) z'))) -> c.Pos x
      bwPart (y ** z' ** isNothing) with (f.bwd (x, y) z')
        bwPart (y ** z' ** ItIsNothing) | Left l = l
        bwPart (y ** z' ** v)           | Right r = absurd v

  public export
  uncurry : c =%> (CartesianClosure d e) -> (c >*< d) =%> e
  uncurry f = !% \(x, y) => ((f.fwd x).fwd y ** bwPart) where
    bwPart : {x : c.Shp} -> {y : d.Shp} ->
      e.Pos ((f.fwd x).fwd y) -> Either (c.Pos x) (d.Pos y)
    bwPart z' with ((f.fwd x).bwd y z') proof p
      bwPart z' | Nothing = Left $ f.bwd x (y ** z' ** rewrite p in ItIsNothing)
      bwPart z' | Just r = Right r

  public export
  apply : (CartesianClosure x y) >*< x =%> y
  apply = uncurry {d=x} id


||| Pair up two extensions into an extension of the Hancock tensor product.
public export
pairExtensions : Ext c a -> Ext d b -> Ext (c >< d) (a, b)
pairExtensions (shapeC <| indexC) (shapeD <| indexD)
  = (shapeC, shapeD) <| \(posC, posD) => (indexC posC, indexD posD)
