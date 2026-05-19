module Data.Container.Additive.Object.Instances

import Data.List.Quantifiers
import Data.Vect.Quantifiers

import Data.Container.Base
import Data.ComMonoid
import Data.Container.Additive.Object.Definition
import Data.Container.Additive.Extension.Definition
import Data.Container.Additive.Product.Definitions

||| Scalar additive container
||| This is equivalent to `!! UnitCont`
||| Unit of the categorical product
public export
Scalar : AddCont
Scalar = MkAddCont Scalar

||| Empty additive container
||| Unit of the coproduct
||| Initial container
public export
Empty : AddCont
Empty = MkAddCont Empty @{MkI absurd}

||| Constant additive container, positions not dependent on shapes
||| Allows the backward part to be different than forward one
public export
Const : Type -> ComMonoid -> AddCont
Const a (t ** m) = MkAddCont (Const2 a t) @{MkI $ \_ => m}

public export
TrivialPos : Type -> AddCont
TrivialPos a = Const a (Unit ** %search)

namespace NumConst
  ||| Like above, but where backward part is same as forward one
  ||| Also arises from Num instance
  public export
  Const : (a : Type) -> (mon : ComMonoid a) => AddCont
  Const a = Const a (a ** mon)