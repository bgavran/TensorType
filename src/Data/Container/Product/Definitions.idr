module Data.Container.Product.Definitions

import Data.DPair
import Decidable.Equality

import Data.Container.Object.Definition
import Data.Container.Extension.Definition

import Misc

public export infixr 0 ><
public export infixr 0 >*<
public export infixr 0 >+<
public export infixr 0 >@
public export infixr 0 @>

||| Categorical product of containers
public export
(>*<) : Cont -> Cont -> Cont
c1 >*< c2 = ((s, s') : (c1.Shp, c2.Shp)) !> Either (c1.Pos s) (c2.Pos s')

||| Non-categorical product of containers, often also called
||| 'Hancock' (Scotland), 'Dirichlet' (Spivak), or 'Tensor product' (various)
||| Monoid with CUnit
public export
(><) : Cont -> Cont -> Cont
c1 >< c2 = (ss : (c1.Shp, c2.Shp)) !> (c1.Pos (fst ss), c2.Pos (snd ss))


||| Coproduct of containers
public export
(>+<) : Cont -> Cont -> Cont
c1 >+< c2 = (es : Either c1.Shp c2.Shp) !> either c1.Pos c2.Pos es

||| Composition of containers making Ext (c >@ d) = (Ext c) . (Ext d)
||| Non-symmetric in general, and not in diagrammatic order
||| Monoid with Scalar
public export
(>@) : Cont -> Cont -> Cont
c >@ d = (ex : Ext c d.Shp) !> (cp : c.Pos (shapeExt ex) ** d.Pos (index ex cp))

||| Diagrammatic composition of containers
public export
(@>) : Cont -> Cont -> Cont
c @> d = (ex : Ext d c.Shp) !> (dp : d.Pos (shapeExt ex) ** c.Pos (index ex dp))

||| Derivative of a container
||| Given c=(Shp !> pos) the derivative can be thought of as
||| a shape s : Shp, a distinguished position p : pos s, and the set of *all other positions*
public export
Derivative : (c : Cont) ->
  InterfaceOnPositions c DecEq =>
  Cont
Derivative (shp !> pos) @{MkI}
  = ((s ** p) : DPair shp pos) !> (p' : pos s ** IsNo (decEq p p'))