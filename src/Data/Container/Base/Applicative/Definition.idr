module Data.Container.Base.Applicative.Definition

import Data.Container.Base.Object.Definition
import Data.Container.Base.Extension.Definition
import Misc

%hide Builtin.infixr.(#)

-- this file and the applicative directory is a relic of the old implementation
-- not all of this is used, and likely can be simplified


||| Applicative Container: a container together with a proof that its extension 
||| is an applicative functor.
||| Equivalent to a monoid in the category of containers with the tensor product
||| i.e. to a monoid on shapes, and for every shape, a comonoid on positions.
||| Currently extensions for ergonomics, and defined using Idris' auto as
||| generally we'd like to avoid directly providing the instance.
||| In the future, perhaps using tensor product formulation will be cleaner
public export
record ContA where
  constructor (#)
  GetC : Cont
  {auto applPrf : Applicative (Ext GetC)}

public export prefix 0 #

||| Convenience functions so we dont have to keep writing GetC
public export
(.Shp) : ContA -> Type
(.Shp) c = (GetC c) .Shp

public export
(.Pos) : (c : ContA) -> c.Shp -> Type
(.Pos) c sh = (GetC c) .Pos sh