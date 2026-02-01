module Data.Container.Additive.Object.Definition

import Data.Container.Base
import Data.ComMonoid

||| Additive container: a container whose every set of positions is a
||| commutative monoid.
||| Not to be confused with `TensorMonoid` where the set of shapes is a monoid,
||| and every set of positions is a comonoid
||| We need additivity only because we want to copy/delete information: on the 
||| backwards pass this sums up or creates a zero value
public export
record AddCont where
  constructor MkAddCont
  UC : Cont
  {auto mon : InterfaceOnPositions UC ComMonoid}

public export
(.Shp) : AddCont -> Type
(.Shp) c = Shp (UC c)

public export
(.Pos) : (c : AddCont) -> c.Shp -> Type
(.Pos) c = Pos (UC c)

||| Underlying monoid structure of positions
public export
UMon : (c : AddCont) -> (s : c.Shp) -> ComMonoid (c.Pos s)
UMon (MkAddCont c @{MkI @{m}}) s = m s

public export
(.Plus) : (c : AddCont) -> (s : c.Shp) -> (c.Pos s -> c.Pos s -> c.Pos s)
(.Plus) c s = plus (UMon c s)

public export
(.Zero) : (c : AddCont) -> (s : c.Shp) -> c.Pos s
(.Zero) c s = neutral (UMon c s)

||| Convenience datatype storing the property that
||| an additive container `c` has an interface `i` on its positions
public export
data InterfaceOnPositions : (c : AddCont) -> (i : Type -> Type) -> Type where
  ||| For every shape s the set of positions c.Pos s has that interface
  MkI : (p : (s : c.Shp) -> i (c.Pos s)) =>
    InterfaceOnPositions c i
