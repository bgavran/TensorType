module Data.Container.Additive.Object.Instances

import Data.List.Quantifiers
import Data.Vect.Quantifiers

import Data.Container.Base
import Data.ComMonoid
import Data.Container.Additive.Object.Definition
import Data.Container.Additive.Extension.Definition
import Data.Container.Additive.Product.Definitions

||| Constant (non-dependent) add. container, positions not dependent on shapes
||| As a polynomial functor: F(Y) = aY^b
public export
Const2 : Type -> ComMonoid -> AddCont
Const2 a (t ** m) = MkAddCont (Const2 a t) @{MkI $ \_ => m}

namespace NumConst
  ||| Constant additive container whose shapes and positions coincide
  ||| Also arises from Num instance
  public export
  Const : (a : Type) -> (mon : ComMonoid a) => AddCont
  Const a = Const2 a (a ** mon)

||| Naperian additive container: a constant container with a single shape
||| As a polynomial functor: F(Y) = Y^b
public export
Nap : ComMonoid -> AddCont
Nap b = Const2 Unit b

||| Flat additive container: a constant container with a single position
||| As a polynomial functor: F(Y) = aY
||| Notably, unlike with `Data.Container.Base`, there is no `Sharp`
public export
Flat : Type -> AddCont
Flat a = Const2 a (Unit ** %search)


||| Empty additive container
||| As a polynomial functor: F(Y) = 0
||| Initial additive container
public export
Empty : AddCont
Empty = MkAddCont Empty @{MkI absurd}


||| Container of a single thing
||| As a polynomial functor: F(Y) = U(Y) where U is forgetful functor
||| Unit of the tensor product
public export
Scalar : AddCont
Scalar = Nap (Nat ** %search)


||| Additive container with a single shape and position
||| As a polynomial functor F(Y) = 1
||| Terminal additive container
public export
UnitCont : AddCont
UnitCont = Const Unit