module Data.Container.Base.Product.Definitions

import Data.DPair
import Decidable.Equality
import Data.Either
import Data.Vect
import Data.List.Quantifiers
import Data.Vect.Quantifiers

import Data.Container.Base.Object.Definition
import Data.Container.Base.Morphism.Definition
import Data.Container.Base.Extension.Definition
import Data.Container.Base.Properties.Definitions


import Data.Container.Base.Quantifiers

import Control.Monad.Distribution
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
||| Monoid with CUnit
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
    (><) f g = !% \(c, d) => ((f.fwd c, g.fwd d) **
      \(c', d') => (f.bwd c c', g.bwd d d'))

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
||| `+` is the pointwise product of functors.
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
  positionCont : (c, d : Cont) -> Ext c d.Shp -> Cont
  positionCont c d ex = (cp : c.Pos (shapeExt ex)) !> d.Pos (index ex cp)
  
  ||| Composition of containers making Ext (c >@ d) = (Ext c) . (Ext d)
  ||| Non-symmetric in general, and not in diagrammatic order
  ||| Monoid with Scalar
  public export
  (>@) : Cont -> Cont -> Cont
  c >@ d = (ex : Ext c d.Shp) !> DPair (positionCont c d ex)

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
    (>@) f g = !% \(s <| idx) => (f.fwd s <| g.fwd . idx . f.bwd s **
      \(dp ** dp2) => (f.bwd s dp ** g.bwd (idx (f.bwd s dp)) dp2))

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

public export infixr 9 <!>
||| If `f` is a monad, then `f <!> -` is a comonad, and vice versa
public export
(<!>) : (f : Type -> Type) -> Cont -> Cont
f <!> c = (s : c.Shp) !> (f (c.Pos s))


namespace Morphism
  public export
  (<!>) : (f : Type -> Type) -> Functor f =>
    c =%> d ->
    f <!> c =%> f <!> d
  f <!> l = !% \x => (l.fwd x ** ((l.bwd x) <$>) )


public export prefix 9 !!
public export prefix 9 !*

||| BANG. List on positions, always has a monoid structure
public export
(!!) : Cont -> Cont
(!!) = (List <!>)

public export
(!*) : Cont -> Cont
(!*) = (Bag <!>)


namespace Morphism
  public export
  (!!) : c =%> d -> !! c =%> !! d
  (!!) = (List <!>)

  public export
  (!*) : c =%> d -> !* c =%> !* d
  (!*) = (Bag <!>)
  

||| Turn a banged container into a container
||| Requires pure on the backward pass
public export
pureBw : Monad m => m <!> c =%> c
pureBw = !% \x => (x ** pure)

public export
joinBw : Monad m => m <!> c =%> m <!> (m <!> c)
joinBw = !% \x => (x ** join)

public export
sumBw : InterfaceOnPositions c ComMonoid => c =%> Bag <!> c
sumBw @{MkI i} = !% \x => (x ** sum @{i x})

public export
coproductBang : m <!> (c >+< d) =%> (m <!> c) >+< (m <!> d)
coproductBang = !% \case
  Left x => (Left x ** id)
  Right y => (Right y ** id)

public export
tensorBang : Applicative m => m <!> (c >< d) =%> (m <!> c) >< (m <!> d)
tensorBang = !% \(x, y) => ((x, y) ** \(mx', my') => [| (mx', my') |])

public export
compositionBang : Monoid d.Shp => !! (c >@ d) =%> (!! c) >@ (!! d)
compositionBang = !% \(cShp <| cPosTodShp) => (cShp <| ?extract **
  \(ma ** mb) => do
    ?fifif)

public export
compositionBangBack : Monad m => (m <!> c) >@ (m <!> d) =%> m <!> (c >@ d)
compositionBangBack = !% \ex => (shapeExt ex <| (index ex) . pure **
  \mdp => ?hmm)

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


-- Not exactly a product
public export
List : Cont -> Cont
List c = (ss : List c.Shp) !> All c.Pos ss

public export
Bag : Cont -> Cont
Bag c = (ss : Bag c.Shp) !> All c.Pos ss

namespace Morphism
  public export
  bww : (f : c =%> d) -> (cs : List c.Shp) ->
    All (d.Pos) (f.fwd <$> cs) -> All (c .Pos) cs
  bww f [] [] = []
  bww f (c :: cs) (a :: as) = (f.bwd c a) :: bww f cs as

  public export
  List : c =%> d -> List c =%> List d
  List f = !% \cs => (f.fwd <$> cs ** bww f cs)




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
Deriv (shp !> pos) @{MkI _}
  = ((s ** p) : DPair shp pos) !> (p' : pos s ** IsNo (decEq p p'))