module Data.Container.Base.Endofunctor.Definition

import Data.List.Quantifiers
import Decidable.Equality

import Data.Container.Base.Object.Definition
import Data.Container.Base.Morphism.Definition
import Data.Container.Base.Properties.Definition

import Data.ComMonoid

import Misc

{-------------------------------------------------------------------------------
Endofunctors and (co)monads on the category of containers.

A monad `m` on Type lifts to `Cont` in two ways:
* On positions (via the `m <!> -` modality)
* On shapes (`ListAll`, `BagAll`,...)
-------------------------------------------------------------------------------}

public export infixr 9 <!>
public export prefix 9 !! -- List : Cont -> Cont
public export prefix 9 !* -- Bag : Cont -> Cont

||| If `f` is a monad, then `f <!> -` is a comonad, and vice versa
public export
(<!>) : (f : Type -> Type) -> Cont -> Cont
f <!> c = (s : c.Shp) !> f (c.Pos s)

namespace Morphism
  public export
  (<!>) : (f : Type -> Type) -> Functor f =>
    c =%> d ->
    f <!> c =%> f <!> d
  f <!> l = !% \x => let (y ** ky) = (%!) l x
                     in (y ** map ky)

||| Comonad of the adjunction between Cont and Cont_Mon
||| BANG. List on positions, always has a monoid structure
public export
(!!) : Cont -> Cont
(!!) = (List <!>)

||| Comonad of the adjunction between Cont and AddCont
||| Bag on positions, always has a commutative monoid structure
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
||| At `m = Bag` this is the counit of `UC -| !*`, i.e. `addContTransposeInv id`
public export
pureBw : Monad m => m <!> c =%> c
pureBw = !% \x => (x ** pure)

public export
joinBw : Monad m => m <!> c =%> m <!> (m <!> c)
joinBw = !% \x => (x ** join)

||| A bag of positions is added up using their monoid structure
||| This is the underlying lens of the unit of `UC -| !*`, i.e. of
||| `addContTranspose id`.
public export
sumBw : InterfaceOnPositions c ComMonoid => c =%> Bag <!> c
sumBw @{MkI i} = !% \x => (x ** sum @{i x})

-- todo which other adjunction structure maps should be here?


namespace FunctorsOnCont
  public export
  ListAll : Cont -> Cont
  ListAll c = (ss : List c.Shp) !> All c.Pos ss

  public export
  ListAny : Cont -> Cont
  ListAny c = (ss : List c.Shp) !> Any c.Pos ss

  public export
  BagAll : Cont -> Cont
  BagAll c = (ss : Bag c.Shp) !> All c.Pos ss

  public export
  unitBag : c =%> BagAll c
  unitBag = !% \x => (MkBag [x] ** qq)
    where qq : List.Quantifiers.All.All (c .Pos) [x] -> c .Pos x
          qq [y] = y

  namespace Morphism
    public export
    bww : (f : c =%> d) -> (cs : List c.Shp) ->
      All (d.Pos) (f.fwd <$> cs) -> All (c .Pos) cs
    bww f [] [] = []
    bww f (c :: cs) (a :: as) = (f.bwd c a) :: bww f cs as

    public export
    List : c =%> d -> ListAll c =%> ListAll d
    List f = !% \cs => (f.fwd <$> cs ** bww f cs)

||| Derivative of a container
||| Given c=(Shp !> pos) the derivative can be thought of as
||| a shape s : Shp, a distinguished position p : pos s, and the set of *all other positions*
public export
Deriv : (c : Cont) ->
  InterfaceOnPositions c DecEq =>
  Cont
Deriv (shp !> pos) @{MkI _}
  = ((s ** p) : DPair shp pos) !> (p' : pos s ** IsNo (decEq p p'))
