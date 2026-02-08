module Data.Container.Additive.Morphism.Instances

import Data.Container.Base
import Data.ComMonoid
import Data.Container.Additive.Object.Definition
import Data.Container.Additive.Object.Instances
import Data.Container.Additive.Morphism.Definition
import Data.Container.Additive.Product.Definitions

%hide Data.Container.Base.Object.Instances.Const

public export
State : {0 c : AddCont} -> (x : c.Shp) -> Scalar =%> c
State x = !%+ \() => (x ** \_ => ())

public export
Costate : {0 c : AddCont} ->
  (s : (x : c.Shp) -> c.Pos x) ->
  c =%> Scalar
Costate s = !%+ \x => (() ** \() => s x)

public export
constantOne : {c : AddCont} ->
  InterfaceOnPositions c Num =>
  c =%> Scalar
constantOne @{MkI @{p}} = Costate {c=c} (\x => let numPos = p x in 1)

public export
rightUnit : {c : AddCont} -> (c >< Scalar) =%> c
rightUnit = !%+ \(x, ()) => (x ** \x' => (x', ()))

public export
rightUnitInv : {c : AddCont} -> c =%> (c >< Scalar)
rightUnitInv = !%+ \x => ((x, ()) ** \(x', ()) => x')

public export
leftUnitInv : {c : AddCont} -> c =%> (Scalar >< c)
leftUnitInv = !%+ \x => (((), x) ** \((), x') => x')

public export
swapMiddle : {c1, c2, c3, c4 : AddCont} ->
  ((c1 >< c2) >< (c3 >< c4)) =%> ((c1 >< c3) >< (c2 >< c4))
swapMiddle = !%+ \((x, y), (z, w)) => (((x, z), (y, w)) **
  \((x', z'), (y', w')) => ((x', y'), (z', w')))

public export
Copy : {c : AddCont} ->
  c =%> (c >< c)
Copy = !%+ \x => ((x, x) ** uncurry (c.Plus x))

public export
Delete : {c : AddCont} ->
  c =%> Scalar
Delete = !%+ \x => (() ** \() => c.Zero x)

public export
Sum : Num a =>
  (Const a >< Const a) =%> Const a
Sum = !%+ \(x1, x2) => (x1 + x2 ** \x' => (x', x'))

public export
Negate : Neg a =>
  Const a =%> Const a
Negate = !%+ \x => (-x ** \x' => -x')

public export
Zero : Num a =>
  Scalar =%> Const a
Zero = State 0

public export
Mul : Num a =>
  (Const a >< Const a) =%> Const a
Mul = !%+ \(x1, x2) => (x1 * x2 ** \x' => (x' * x2, x' * x1))

||| Mean squared error
public export
MSE : (Const Double >< Const Double) =%> (Const Double)
MSE = ((><) {c1=Const Double} id Negate) %>> Sum %>> Copy %>> Mul

