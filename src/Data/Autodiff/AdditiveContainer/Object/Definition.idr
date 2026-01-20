module Data.Autodiff.AdditiveContainer.Object.Definition

import Data.Container
import Data.ComMonoid

||| Additive container: a container whose every set of positions is a monoid.
||| Not to be confused with Applicative containers where the set of shapes is
||| a monoid, and every set of positions is a comonoid
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