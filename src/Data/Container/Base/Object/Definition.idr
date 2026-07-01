module Data.Container.Base.Object.Definition

||| Containers capture the idea that datatypes consist of groups of memory 
||| locations where data can be stored. Locations for a particular group are 
||| referred to as 'positions' and a particular group is referred to as a
||| 'shape'.
public export
record Cont where
  constructor (!>)
  ||| A type of shapes
  Shp : Type
  ||| For each shape, a set of positions
  Pos : Shp -> Type

export typebind infixr 0 !>

%name Cont c, c', c''

public export
DPair : Cont -> Type
DPair c = (x : c.Shp ** c.Pos x)

||| Synonym for `DPair`. The idea is that we can think of a sigma type of 
||| a container as a a choice of a shape, and a sequence of choices
||| (the "path") to reach a particular position.
||| This isn't as easily seen for containers not defined as fixpoints, where
||| these "choices" are not made using container machinery, but directly in 
||| Idris. But for n-ary containers this becomes more apparent
public export
Path : Cont -> Type
Path = DPair
