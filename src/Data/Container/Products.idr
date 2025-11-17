module Data.Container.Products

import Data.DPair
import Decidable.Equality

import Data.Container.Object.Definition
import Data.Container.Extension.Definition

import Misc

public export infixr 0 ><
public export infixr 0 >*<
public export infixr 0 >+<
public export infixr 0 >@

||| Categorical product of containers
public export
(>*<) : Cont -> Cont -> Cont
c1 >*< c2 = ((s, s') : (c1.Shp, c2.Shp)) !> Either (c1.Pos s) (c2.Pos s')

||| Non-categorical product of containers, often also called
||| 'Hancock' (Scotland), 'Dirichlet' (Spivak), or 'Tensor product' (various)
||| Monoid with CUnit
public export
(><) : Cont -> Cont -> Cont
c1 >< c2 = ((s, s') : (c1.Shp, c2.Shp)) !> (c1.Pos s, c2.Pos s')


||| Coproduct of containers
public export
(>+<) : Cont -> Cont -> Cont
c1 >+< c2 = (es : Either c1.Shp c2.Shp) !> (case es of
  Left s => c1.Pos s
  Right s' => c2.Pos s')

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
shapesOnly : (a : Type) -> Cont
shapesOnly a = (x : a) !> Void

public export
DecEq Void where
  decEq x1 _ = void x1

shapesIoP : InterfaceOnPositions (shapesOnly a) DecEq
shapesIoP = MkI

derivConst : (a : Type) -> Ext (Deriv (shapesOnly a)) Integer
