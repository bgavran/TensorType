module Data.Container.Applicative.Definition

import Data.Container.Object.Definition
import Data.Container.Extension.Definition
import Misc

%hide Builtin.infixr.(#)

-- TODO this will soon be deprecated


||| Applicative Container
||| Consists of a container and a proof that its extension is an applicative functor
||| Defined using Idris' auto as we'd like to avoid directly providing this
public export
record ContA where
  constructor (#)
  GetC : Cont
  ||| Question: can we state this without referencing the extension?
  {auto applPrf : Applicative (Ext GetC)}

public export prefix 0 #

||| Convenience functions so we dont have to keep writing GetC
public export
(.Shp) : ContA -> Type
(.Shp) c = (GetC c) .Shp

public export
(.Pos) : (c : ContA) -> c.Shp -> Type
(.Pos) c sh = (GetC c) .Pos sh