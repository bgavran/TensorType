module Data.CT.Functor.Definition

import Data.CT.Category.Definition

public export
record Functor (c, d : Cat) where
  constructor MkFunctor
  0 mapObj : c.Obj -> d.Obj
  0 mapMor : {x, y : c.Obj} -> c.Hom x y -> d.Hom (mapObj x) (mapObj y)

public export
composeFunctors : Functor c d -> Functor d e -> Functor c e
composeFunctors f g = MkFunctor
  (g.mapObj . f.mapObj)
  (g.mapMor . f.mapMor)

