module Data.Tensor.Shape.Axis

import Data.Vect.Quantifiers

import Data.Container.Base
import Misc

||| The name for an axis is an arbitrary string
public export
AxisName : Type
AxisName = String

||| An axis is a container together with its name
public export
record Axis where
  constructor (~>)
  name : AxisName
  cont : Cont

public export infixr 0 ~> -- Constructor for container-based axes
public export infixr 0 ~~> -- 'Constructor' for cubical axes

public export
rename : Axis -> AxisName -> Axis
rename a str = str ~> a.cont

||| In some cases we TensorType might need to assign a default name to an axis,
||| one which is internal and will not be exposed to the user.
||| This is the default name for such cases
public export
TTInternalName : AxisName
TTInternalName = "__tensortype_tempaxis__"

namespace Cubical
  ||| A "constructor" for cubical axes
  public export
  (~~>) : AxisName -> Nat -> Axis
  (~~>) axisName n = axisName ~> Vect n

  ||| Follows the pattern of `IsCubical` from `Base.Object.Definition`
  public export
  data IsCubical : Axis -> Type where
    MkIsCubical : (name : AxisName) -> (n : Nat) -> IsCubical (name ~~> n)

  ||| Evidence of axis cubicality -> evidence of underlying container cubicality
  public export
  toContCubical : {0 a : Axis} -> IsCubical a -> IsCubical a.cont
  toContCubical (MkIsCubical _ n) = MkIsCubical n

  ||| Extract the dimension from IsCubical with axis implicit
  public export
  dimHelper : {0 a : Axis} -> IsCubical a -> Nat
  dimHelper (MkIsCubical _ n) = n

  ||| Extract the dimension from an axis which we know is cubical
  public export
  dim : (0 a : Axis) -> IsCubical a => Nat
  dim _ @{ic} = dimHelper ic

  ||| Extract the dimensions of cubical axes, with shape implicit
  public export
  dimsHelper : {0 shape : Vect r Axis} ->
    All IsCubical shape -> List Nat
  dimsHelper [] = []
  dimsHelper (ic :: ns) = dimHelper ic :: dimsHelper ns

  ||| Extract the dimensions of cubical axes, with shape explicit
  public export
  dims : (0 shape : Vect r Axis) -> All IsCubical shape => List Nat
  dims _ @{ac} = dimsHelper ac

  ||| Product of all the dimensions of a cubical tensors, i.e. its size
  public export
  size : (0 shape : Vect r Axis) -> (ac : All IsCubical shape) => Nat
  size shape = prod (dims shape)

namespace Naperian
  ||| Follows the pattern of `IsNaperian` from `Base.Object.Definition`
  public export
  data IsNaperian : Axis -> Type where
    MkIsNaperian : (name : AxisName) -> (pos : Type) ->
      IsNaperian (name ~> Nap pos)

  ||| Evidence of axis being Naperian -> evidence of container being Naperian
  %hint
  public export
  toContNaperian : {0 a : Axis} -> IsNaperian a -> IsNaperian a.cont
  toContNaperian (MkIsNaperian _ pos) = MkIsNaperian pos
  
  ||| Extract the position type from IsNaperian with axis implicit
  public export
  LogHelper : {0 a : Axis} -> IsNaperian a => Type
  LogHelper @{MkIsNaperian _ pos} = pos

  ||| Extract the position type from an axis which we know is Naperian
  public export
  Log : (0 a : Axis) -> IsNaperian a => Type
  Log a @{inn} = LogHelper @{inn}

namespace IsConcrete
  public export
  data IsConcrete : Axis -> Type where
    MkIsConcrete : (name : AxisName) -> IsConcrete c -> IsConcrete (name ~> c)

  public export
  toContConcrete : {0 a : Axis} -> IsConcrete a -> IsConcrete a.cont
  toContConcrete (MkIsConcrete _ ic) = ic